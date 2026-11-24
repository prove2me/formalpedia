-- Prove2me | solution 2 for EquivarianceConvolution.gcnn_iff_equivariant_layers
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:32:12.343955+00:00
-- url     : https://prove2.me/submissions/46cf0733-ad01-4c96-bfe8-a64bfdb093fc

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

universe u

namespace EquivarianceConvolution

open scoped BigOperators

theorem ec1_smul_mk {G : Type*} [Group G] (H : Subgroup G) (g u : G) :
    g • ((u : G) : G ⧸ H) = ((g * u : G) : G ⧸ H) :=
  MulAction.Quotient.smul_mk H g u

theorem ec1_smul_eq_one_iff {G : Type*} [Group G] (H : Subgroup G) (g u : G) :
    g⁻¹ • ((u : G) : G ⧸ H) = ((1 : G) : G ⧸ H) ↔ ((g : G) : G ⧸ H) = (u : G ⧸ H) := by
  rw [ec1_smul_mk, QuotientGroup.eq, QuotientGroup.eq]
  rw [← Subgroup.inv_mem_iff]
  simp

theorem ec1_card_fiber {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    [DecidableEq (G ⧸ H)] (u : G) :
    (Finset.univ.filter (fun g : G => ((g : G) : G ⧸ H) = (u : G ⧸ H))).card = Nat.card H := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun g => ⟨u⁻¹ * g.1, QuotientGroup.eq.1 g.2.symm⟩
      invFun := fun h => ⟨u * h.1, QuotientGroup.eq.2 (by simp [h.2]) |>.symm⟩
      left_inv := fun g => by ext; simp
      right_inv := fun h => by ext; simp }


/-- A convolution layer is equivariant. -/
theorem ec1_conv_equivariant {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) → (G ⧸ K → Fin n → ℂ)) (hφ : IsConvLayer H K φ) :
    IsEquivariantMap G φ := by
  obtain ⟨χ, -, hχ⟩ := hφ
  intro g f
  funext x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 := hχ (translateFun g f) u
  have h2 := hχ f (g⁻¹ * u)
  simp only [liftQ, vecConv] at h1 h2
  simp only [translateFun, ec1_smul_mk] at h1 ⊢
  rw [h1, h2]
  simp only [mul_assoc]

/-- The impulse at the origin coset in channel `b`. -/
noncomputable def ec1_delta {G : Type*} [Group G] (H : Subgroup G) (m : ℕ) (b : Fin m) :
    G ⧸ H → Fin m → ℂ := by
  classical
  exact fun x => if x = ((1 : G) : G ⧸ H) then Pi.single b 1 else 0

theorem ec1_decomp {G : Type*} [Group G] [Fintype G] (H : Subgroup G) {m : ℕ}
    (f : G ⧸ H → Fin m → ℂ) :
    f = ((Nat.card H : ℂ)⁻¹) • ∑ g : G, ∑ b : Fin m,
      f ((g : G) : G ⧸ H) b • translateFun g (ec1_delta H m b) := by
  classical
  funext x a
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [translateFun, ec1_delta, ec1_smul_eq_one_iff, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  have key : ∀ x : G, ∑ b : Fin m, f ((x : G) : G ⧸ H) b *
      (if ((x : G) : G ⧸ H) = (u : G ⧸ H) then (Pi.single b (1 : ℂ) : Fin m → ℂ) else 0) a =
      if ((x : G) : G ⧸ H) = (u : G ⧸ H) then f (u : G ⧸ H) a else 0 := by
    intro x
    split_ifs with hx
    · rw [hx]; simp [Pi.single_apply]
    · simp
  simp_rw [key]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, ec1_card_fiber,
    nsmul_eq_mul]
  have hpos : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  field_simp


theorem ec1_delta_fixed {G : Type*} [Group G] (H : Subgroup G) (m : ℕ) (b : Fin m)
    (h : G) (hh : h ∈ H) : translateFun h (ec1_delta H m b) = ec1_delta H m b := by
  classical
  funext x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H) :=
    QuotientGroup.eq.2 (by simpa using H.inv_mem hh)
  simp only [translateFun, ec1_delta, ec1_smul_eq_one_iff, h1]
  simp only [eq_comm]

theorem ec1_equivariant_conv {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) →ₗ[ℂ] (G ⧸ K → Fin n → ℂ)) (hφ : IsEquivariantMap G ⇑φ) :
    IsConvLayer H K ⇑φ := by
  have hφ' : ∀ (g : G) (f : G ⧸ H → Fin m → ℂ), φ (translateFun g f) = translateFun g (φ f) :=
    hφ
  refine ⟨fun v a b => (Nat.card H : ℂ)⁻¹ * φ (ec1_delta H m b) ((v : G) : G ⧸ K) a, ?_, ?_⟩
  · intro h hh k hk v
    ext a b
    have e1 : ((h * v * k : G) : G ⧸ K) = ((h * v : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by rw [show (h * v * k)⁻¹ * (h * v) = k⁻¹ by group]; exact K.inv_mem hk)
    have e2 := congrFun (hφ' h⁻¹ (ec1_delta H m b)) ((v : G) : G ⧸ K)
    rw [ec1_delta_fixed H m b h⁻¹ (H.inv_mem hh)] at e2
    simp only [translateFun, inv_inv, ec1_smul_mk] at e2
    simp only [e1, ← e2]
  · intro f u
    have e : φ f = ((Nat.card H : ℂ)⁻¹) • ∑ g : G, ∑ b : Fin m,
        f ((g : G) : G ⧸ H) b • translateFun g (φ (ec1_delta H m b)) := by
      conv_lhs => rw [ec1_decomp H f]
      simp only [map_smul, map_sum, hφ']
    funext a
    simp only [liftQ, vecConv, e, translateFun, ec1_smul_mk, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight u)) _ _ (fun g => ?_)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, mul_inv_rev, inv_inv,
      mul_inv_cancel_left, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring


theorem ec1_net_equivariant {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d)
    (hE : ∀ l < L, IsEquivariantMap G ⇑(N.phi l)) : IsEquivariantNet G L N := by
  intro g f₀ l hl
  induction l with
  | zero => rfl
  | succ l ih =>
    funext x
    have e := congrFun (hE l (by omega) g (N.act l f₀)) x
    simp only [FeedForwardNet.act, ih (by omega), e]
    rfl

end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) :
    (IsGCNN H L N → IsEquivariantNet G L N) ∧
      (IsGCNN H L N ↔ ∀ l < L, IsEquivariantMap G ⇑(N.phi l)) :=
  ⟨fun hN => ec1_net_equivariant H L N
      (fun l hl => ec1_conv_equivariant (H l) (H (l + 1)) _ (hN l hl)),
    ⟨fun hN l hl => ec1_conv_equivariant (H l) (H (l + 1)) _ (hN l hl),
      fun hE l hl => ec1_equivariant_conv (H l) (H (l + 1)) (N.phi l) (hE l hl)⟩⟩
