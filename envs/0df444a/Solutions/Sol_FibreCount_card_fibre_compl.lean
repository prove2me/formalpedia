-- Prove2me | solution 1 for FibreCount.card_fibre_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:14.94322+00:00
-- url     : https://prove2.me/submissions/2e4ec9b8-a8a4-445d-a2ba-eddc0d7e5bb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_CardFibreCompl
import Theorems.Thm_FibreCount_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open FibreCount
open Classical
namespace FibreCount
theorem _root_.solution {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (z : Fin k → V) (hz : LinearIndependent K z)
    (a : U) :
    Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      if a ∈ span K (Set.range (fun j => φ (z j))) then
        Fintype.card K ^ finrank K (LinearMap.ker φ) -
          Fintype.card K ^ (k - finrank K (span K (Set.range (fun j => φ (z j)))))
      else Fintype.card K ^ finrank K (LinearMap.ker φ) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Fintype V := Fintype.ofFinite V

  let ψ : (Fin k → K) →ₗ[K] U :=
    { toFun := fun c => φ (∑ j, c j • z j)
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul,
          RingHom.id_apply] }
  have hψ : LinearMap.range ψ = span K (Set.range (fun j => φ (z j))) := by
    ext u
    rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
    refine exists_congr fun c => ?_
    show φ (∑ j, c j • z j) = u ↔ _
    rw [map_sum]
    simp only [map_smul]

  have hin : Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} = Nat.card {c : Fin k → K // ψ c = a} := by
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun c => ⟨∑ j, c.1 j • z j, ?_, c.2⟩) ⟨?_, ?_⟩
    · exact (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨c.1, rfl⟩
    · intro c d hcd
      have h := congrArg Subtype.val hcd
      simp only at h
      have h0 : ∑ j, (c.1 j - d.1 j) • z j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]
      exact Subtype.ext (funext fun j => sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hz _ h0 j))
    · intro x
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp x.2.1
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      show φ (∑ j, c j • z j) = a
      rw [hc]; exact x.2.2

  have hsplit : Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      Nat.card {x : V // φ x = a} - Nat.card {x : V // x ∈ span K (Set.range z) ∧ φ x = a} := by
    have e : {x : V // φ x = a} ≃
        {x : V // x ∈ span K (Set.range z) ∧ φ x = a} ⊕ {x : V // x ∉ span K (Set.range z) ∧ φ x = a} :=
      { toFun := fun x => if h : x.1 ∈ span K (Set.range z) then Sum.inl ⟨x.1, h, x.2⟩
          else Sum.inr ⟨x.1, h, x.2⟩
        invFun := fun s => Sum.elim (fun y => ⟨y.1, y.2.2⟩) (fun y => ⟨y.1, y.2.2⟩) s
        left_inv := fun x => by
          by_cases h : x.1 ∈ span K (Set.range z) <;> simp [h]
        right_inv := fun s => by
          rcases s with y | y <;> simp [y.2.1] }
    have h := Nat.card_congr e
    rw [Nat.card_sum] at h
    omega
  obtain ⟨x0, hx0⟩ := hφ a
  rw [hsplit, card_fibre φ a x0 hx0, hin]
  split_ifs with ha
  · rw [← hψ] at ha
    obtain ⟨c0, hc0⟩ := ha
    rw [card_fibre ψ a c0 hc0]
    congr 2
    have hrk := LinearMap.finrank_range_add_finrank_ker ψ
    rw [Module.finrank_fin_fun, hψ] at hrk
    omega
  · have h0 : Nat.card {c : Fin k → K // ψ c = a} = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun c => ha ?_⟩
      rw [← hψ]
      exact ⟨c.1, c.2⟩
    rw [h0, Nat.sub_zero]
end FibreCount
