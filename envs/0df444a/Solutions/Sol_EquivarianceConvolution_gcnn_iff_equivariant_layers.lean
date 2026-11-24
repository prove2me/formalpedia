-- Prove2me | solution 1 for EquivarianceConvolution.gcnn_iff_equivariant_layers
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-24T07:00:50.043065+00:00
-- url     : https://prove2.me/submissions/d866f4f7-d9b4-42c2-83d1-ab496b522c12

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

namespace GcnnAux

variable {G : Type*} [Group G] [Fintype G]

open Classical

theorem smul_mk (H : Subgroup G) (g u : G) :
    (g • (u : G ⧸ H) : G ⧸ H) = ((g * u : G) : G ⧸ H) :=
  MulAction.Quotient.smul_mk H g u

/-- a convolution layer is equivariant -/
theorem conv_equivariant (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) → (G ⧸ K → Fin n → ℂ)) (hφ : IsConvLayer H K φ) :
    IsEquivariantMap G φ := by
  obtain ⟨χ, -, hχ⟩ := hφ
  intro g f
  funext x
  induction x using QuotientGroup.induction_on with
  | H u =>
    have h1 := hχ (translateFun g f) u
    have h2 := hχ f (g⁻¹ * u)
    simp only [liftQ] at h1 h2
    rw [h1]
    simp only [translateFun, smul_mk]
    rw [h2]
    simp only [vecConv, liftQ, translateFun, smul_mk, mul_assoc]

/-- layer-wise equivariance gives an equivariant network -/
theorem net_equivariant (H : ℕ → Subgroup G) {d : ℕ → ℕ} (L : ℕ)
    (N : FeedForwardNet (fun l => G ⧸ H l) d)
    (h : ∀ l < L, IsEquivariantMap G ⇑(N.phi l)) : IsEquivariantNet G L N := by
  intro g f₀ l hl
  induction l with
  | zero => rfl
  | succ l ih =>
    have ih' := ih (Nat.le_of_succ_le hl)
    funext x
    simp only [FeedForwardNet.act]
    rw [ih', h l (Nat.lt_of_succ_le hl)]
    rfl

open Classical in
theorem sum_mk (H : Subgroup G) (F : G ⧸ H → ℂ) :
    ∑ w : G, F (w : G ⧸ H) = (Fintype.card H : ℂ) * ∑ y : G ⧸ H, F y := by
  set e := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  rw [← e.symm.sum_comp]
  have hfst : ∀ p : (G ⧸ H) × H, ((e.symm p : G) : G ⧸ H) = p.1 := by
    intro p
    have := congrArg Prod.fst (e.apply_symm_apply p)
    rw [← this]
    rfl
  simp only [hfst]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- basis functions -/
noncomputable def E (H : Subgroup G) {m : ℕ} (y : G ⧸ H) (j : Fin m) : G ⧸ H → Fin m → ℂ :=
  Pi.single y (Pi.single j 1)

theorem translate_E (H : Subgroup G) {m : ℕ} (u : G) (y : G ⧸ H) (j : Fin m) :
    translateFun u⁻¹ (E H y j) = E H (u⁻¹ • y) j := by
  funext x
  simp only [translateFun, inv_inv, E]
  by_cases hx : x = u⁻¹ • y
  · subst hx; simp
  · have : u • x ≠ y := by
      intro h; apply hx; rw [← h, inv_smul_smul]
    simp [Pi.single_apply, hx, this]

theorem phi_E_at (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) →ₗ[ℂ] (G ⧸ K → Fin n → ℂ)) (hφ : IsEquivariantMap G ⇑φ)
    (u : G) (y : G ⧸ H) (j : Fin m) :
    φ (E H y j) (u : G ⧸ K) = φ (E H (u⁻¹ • y) j) ((1 : G) : G ⧸ K) := by
  rw [← translate_E, hφ]
  simp only [translateFun, inv_inv, smul_mk, mul_one]

theorem decomp (H : Subgroup G) {m : ℕ} [Fintype (G ⧸ H)] (f : G ⧸ H → Fin m → ℂ) :
    f = ∑ y, ∑ j, f y j • E H y j := by
  funext y' j'
  simp only [E, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp [Finset.sum_ite_eq, apply_ite (fun F : Fin m → ℂ => F j')]
  simp [Pi.single_apply]

/-- an equivariant linear map is a convolution layer -/
theorem equivariant_conv (H K : Subgroup G) {m n : ℕ}
    (φ : (G ⧸ H → Fin m → ℂ) →ₗ[ℂ] (G ⧸ K → Fin n → ℂ)) (hφ : IsEquivariantMap G ⇑φ) :
    IsConvLayer H K ⇑φ := by
  classical
  set c : ℂ := ((Fintype.card H : ℂ))⁻¹ with hc
  have hcard : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let χ : G → Matrix (Fin n) (Fin m) ℂ := fun v i j =>
    c * φ (E H ((v⁻¹ : G) : G ⧸ H) j) ((1 : G) : G ⧸ K) i
  refine ⟨χ, ?_, ?_⟩
  · intro h hh k hk v
    funext i j
    simp only [χ]
    congr 2
    have h1 : (((h * v * k)⁻¹ : G) : G ⧸ H) = k⁻¹ • ((v⁻¹ : G) : G ⧸ H) := by
      rw [smul_mk, QuotientGroup.eq]
      have : (h * v * k)⁻¹⁻¹ * (k⁻¹ * v⁻¹) = h := by group
      rw [this]; exact hh
    rw [h1, ← phi_E_at H K φ hφ k]
    have h2 : ((k : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by
      rw [QuotientGroup.eq]; simpa using K.inv_mem hk
    rw [h2]
  · intro f u
    funext i
    simp only [liftQ, vecConv]
    -- left side via the basis decomposition
    conv_lhs => rw [decomp H f]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [phi_E_at H K φ hφ u]
    -- right side: reindex `v ↦ w = u v⁻¹`
    simp only [Matrix.mulVec, dotProduct, χ]
    let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulRight u)
    have he : ∀ w, e w = w⁻¹ * u := fun w => rfl
    rw [← e.sum_comp]
    have hinv : ∀ w : G, (e w)⁻¹ = u⁻¹ * w := by intro w; rw [he]; group
    simp only [hinv, mul_inv_cancel_left]
    have hq : ∀ w : G, ((u⁻¹ * w : G) : G ⧸ H) = u⁻¹ • ((w : G) : G ⧸ H) :=
      fun w => (smul_mk H u⁻¹ w).symm
    simp only [hq]
    rw [sum_mk H (fun y => ∑ j, c * φ (E H (u⁻¹ • y) j) ((1 : G) : G ⧸ K) i * f y j)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc]
    field_simp

end GcnnAux

end EquivarianceConvolution

open EquivarianceConvolution EquivarianceConvolution.GcnnAux in
theorem solution {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) :
    (IsGCNN H L N → IsEquivariantNet G L N) ∧
      (IsGCNN H L N ↔ ∀ l < L, IsEquivariantMap G ⇑(N.phi l)) := by
  have hfwd : IsGCNN H L N → ∀ l < L, IsEquivariantMap G ⇑(N.phi l) := fun h l hl =>
    conv_equivariant (H l) (H (l + 1)) _ (h l hl)
  refine ⟨fun h => net_equivariant H L N (hfwd h), hfwd, fun h l hl => ?_⟩
  exact equivariant_conv (H l) (H (l + 1)) (N.phi l) (h l hl)
