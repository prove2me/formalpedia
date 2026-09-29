-- Prove2me | solution 1 for CuspidalType.iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7fa6f5d6-145b-5391-aed0-412bdb85ee77

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem

set_option autoImplicit false

private theorem w5c_mem_iff {q : ℕ} [Fact q.Prime] {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K (CuspidalType.GL2 q) V) (x : V) :
    x ∈ (⨅ g : CuspidalType.GL2 q,
        LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g)) ↔
      ∀ g : CuspidalType.GL2 q, ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (ρ g x) = 0 := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.comp_apply]

private theorem w5c_inf_span_eq_bot {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] (ρ : Representation K (CuspidalType.GL2 q) V) (C : Submodule K V)
    (hC : ∀ x : V, x ∈ C ↔
      ∀ g : CuspidalType.GL2 q, ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (ρ g x) = 0) :
    C ⊓ Submodule.span K {x : V | ∃ (g : CuspidalType.GL2 q) (v : V),
      (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) ∧ ρ g v = x} = ⊥ := by
  haveI : Nonempty (CuspidalType.GL2 q) := ⟨1⟩
  haveI : Nonempty (ZMod q) := ⟨0⟩
  have hcard : (Fintype.card (CuspidalType.GL2 q) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hq : (Fintype.card (ZMod q) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  have hstab : ∀ (h : CuspidalType.GL2 q), ∀ x ∈ C, ρ h x ∈ C := by
    intro h x hx
    rw [hC] at hx ⊢
    intro g
    have key : ρ g (ρ h x) = ρ (g * h) x := by rw [map_mul, Module.End.mul_apply]
    rw [key]
    exact hx (g * h)

  have hcomm : ∀ (L : V →ₗ[K] V), (∀ (g : CuspidalType.GL2 q) (y : V), L (ρ g y) = ρ g (L y)) →
      ∀ y : V, ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (L y) =
        L (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) y) := by
    intro L hL y
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => (hL _ y).symm

  obtain ⟨π, hπC, hπid⟩ : ∃ π : V →ₗ[K] V, (∀ v, π v ∈ C) ∧ ∀ x ∈ C, π x = x := by
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_leftInverse_of_injective C.subtype (Submodule.ker_subtype C)
    refine ⟨C.subtype ∘ₗ ℓ, fun v => (ℓ v).2, fun x hx => ?_⟩
    have h1 : ℓ x = ⟨x, hx⟩ := by
      have h0 := LinearMap.congr_fun hℓ ⟨x, hx⟩
      rwa [LinearMap.comp_apply, LinearMap.id_apply, Submodule.subtype_apply] at h0
    exact congrArg Subtype.val h1

  obtain ⟨P, hP⟩ : ∃ P : V →ₗ[K] V, ∀ v, P v = ∑ g : CuspidalType.GL2 q, ρ g (π (ρ g⁻¹ v)) :=
    ⟨∑ g : CuspidalType.GL2 q, ρ g ∘ₗ π ∘ₗ ρ g⁻¹, fun v => by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]⟩
  have hPcomm : ∀ (h : CuspidalType.GL2 q) (v : V), P (ρ h v) = ρ h (P v) := by
    intro h v
    have hsum : ∑ g : CuspidalType.GL2 q, ρ h (ρ g (π (ρ g⁻¹ v))) =
        ∑ g : CuspidalType.GL2 q, ρ g (π (ρ g⁻¹ (ρ h v))) := by
      refine Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ fun g => ?_
      show ρ h (ρ g (π (ρ g⁻¹ v))) = ρ (h * g) (π (ρ (h * g)⁻¹ (ρ h v)))
      have e1 : ρ (h * g)⁻¹ (ρ h v) = ρ g⁻¹ v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
      have e2 : ρ (h * g) (π (ρ g⁻¹ v)) = ρ h (ρ g (π (ρ g⁻¹ v))) := by
        rw [map_mul, Module.End.mul_apply]
      rw [e1, e2]
    rw [hP, hP, map_sum]
    exact hsum.symm
  have hPC : ∀ v : V, P v ∈ C := by
    intro v
    rw [hP]
    exact Submodule.sum_mem _ fun g _ => hstab g _ (hπC _)
  have hPid : ∀ x ∈ C, P x = (Fintype.card (CuspidalType.GL2 q) : K) • x := by
    intro x hx
    have e : ∀ g : CuspidalType.GL2 q, ρ g (π (ρ g⁻¹ x)) = x := by
      intro g
      rw [hπid _ (hstab g⁻¹ x hx), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [hP, Finset.sum_congr rfl fun g _ => e g, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]

  have hPfix : ∀ v : V, (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) → P v = 0 := by
    intro v hv
    have h1 : ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) v = (Fintype.card (ZMod q) : K) • v := by
      rw [Finset.sum_congr rfl fun t _ => hv t, Finset.sum_const, Finset.card_univ,
        Nat.cast_smul_eq_nsmul]
    have h2 : ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (P v) = 0 := by
      have h3 := (hC (P v)).mp (hPC v) 1
      rwa [map_one, Module.End.one_apply] at h3
    rw [hcomm P hPcomm v, h1, map_smul] at h2
    exact (eq_zero_or_eq_zero_of_smul_eq_zero h2).resolve_left hq
  have hW : Submodule.span K {x : V | ∃ (g : CuspidalType.GL2 q) (v : V),
      (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) ∧ ρ g v = x} ≤ LinearMap.ker P := by
    rw [Submodule.span_le]
    rintro x ⟨g, v, hv, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hPcomm, hPfix v hv, map_zero]

  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  have h1 : P x = 0 := LinearMap.mem_ker.mp (hW hx.2)
  rw [hPid x hx.1] at h1
  exact (eq_zero_or_eq_zero_of_smul_eq_zero h1).resolve_left hcard

theorem
    solution
    (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (ρ : Representation K (CuspidalType.GL2 q) V) (τ : V →ₗ[K] V)
    (hτ : ∀ g : CuspidalType.GL2 q, τ ∘ₗ ρ g = ρ g ∘ₗ τ)
    (T : Submodule K V)
    (hT : T ≤ Submodule.span K {x : V | ∃ (g : CuspidalType.GL2 q) (v : V),
      (∀ t : ZMod q, ρ (CuspidalType.unipotent q t) v = v) ∧ ρ g v = x})
    (hτT : ∀ v : V, τ v - v ∈ T) :
    (⨅ g : CuspidalType.GL2 q,
        LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g)) ⊓ T = ⊥ ∧
      ∀ v ∈ ⨅ g : CuspidalType.GL2 q,
        LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g), τ v = v := by
  have hmem := w5c_mem_iff ρ
  have hcore := w5c_inf_span_eq_bot ρ _ hmem
  have hbot : (⨅ g : CuspidalType.GL2 q,
      LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g)) ⊓ T = ⊥ :=
    le_antisymm (le_trans (inf_le_inf_left _ hT) hcore.le) bot_le
  refine ⟨hbot, fun v hv => ?_⟩

  have hτC : τ v ∈ ⨅ g : CuspidalType.GL2 q,
      LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g) := by
    rw [hmem] at hv ⊢
    intro g
    have e1 : ρ g (τ v) = τ (ρ g v) := (LinearMap.congr_fun (hτ g) v).symm
    have e2 : ∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (τ (ρ g v)) =
        τ (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) (ρ g v)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun t _ =>
        (LinearMap.congr_fun (hτ (CuspidalType.unipotent q t)) (ρ g v)).symm
    rw [e1, e2, hv g, map_zero]
  have hsub : τ v - v ∈ (⨅ g : CuspidalType.GL2 q,
      LinearMap.ker (∑ t : ZMod q, ρ (CuspidalType.unipotent q t) ∘ₗ ρ g)) ⊓ T :=
    Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hτC hv, hτT v⟩
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hsub
  exact hsub

end S_CuspidalType_iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem
end P2MW
export P2MW.S_CuspidalType_iInf_ker_sum_unipotent_comp_inf_eq_bot_and_apply_eq_self_of_le_span_unipotent_fixed_of_sub_mem (solution)
