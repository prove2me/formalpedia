-- Prove2me | solution 1 for Formalism.CyclotomicNorms.central_scalar_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:40.581905+00:00
-- url     : https://prove2.me/submissions/686e5cb2-9428-4a45-a1a6-ac48dfe26539

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_extN_agree
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_contr_agree
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_nat_identity
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_prism_eq
import Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_prism_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open CentralScalarSequence
namespace Formalism.CyclotomicNorms
theorem _root_.solution : CentralScalar := by
  intro G R W _ _ _ _ _ _ _ ρ z c hz hc hρz
  have hzc : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  obtain ⟨u, hu⟩ := hc
  refine ⟨?_, ?_⟩
  · intro w hw
    have h1 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← hρz, hw, sub_self]
    calc w = ((↑u⁻¹ : R) * ↑u) • w := by simp
      _ = (↑u⁻¹ : R) • ((c - 1) • w) := by rw [mul_smul, hu]
      _ = 0 := by rw [h1, smul_zero]
  · intro n f hf hcoc
    refine ⟨fun x => (↑u⁻¹ : R) • prism R z f x,
      (continuous_of_discreteTopology (f := fun w : W => (↑u⁻¹ : R) • w)).comp
        (prism_continuous z f hf), ?_⟩
    funext g
    have key : coboundary ρ n (prism R z f) g = (c - 1) • f g := by
      set y := extN g with hy
      have hg := extN_agree g
      rw [← hy] at hg
      simp only [coboundary]
      rw [prism_eq z f (fun i => g i.succ) (fun k => y (k + 1)) (fun k => by simp [hg])]
      have hsum : ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • prism R z f (Fin.contractNth j (· * ·) g)
          = ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
            ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
          ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k)) (n + 1)]
        refine sum_congr rfl fun j _ => ?_
        rw [prism_eq z f _ (contrN j y) (contr_agree j g y hg)]
      rw [hsum]
      rw [show f g = f (fun k => y k) from congrArg f (funext hg), sub_smul, one_smul, ← hρz,
        hg 0, Fin.val_zero]
      refine nat_identity ρ z hzc n (fun v => f (fun k => v k)) ?_ y ?_
      · intro u v huv
        exact congrArg f (funext fun k => huv k k.isLt)
      · intro i hi
        have := congrFun hcoc (fun k : Fin (n + 2) => insN i z y k)
        simp only [coboundary, Pi.zero_apply] at this
        have hsum : ∑ j : Fin (n + 2), (-1 : R) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k)) =
            ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • f (fun k => contrN j (insN i z y) k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
            f (fun k => contrN j (insN i z y) k)) (n + 2)]
          refine sum_congr rfl fun j _ => ?_
          rw [show Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k) =
            fun k : Fin (n + 1) => contrN j (insN i z y) k from
              funext (contr_agree j _ _ fun _ => rfl)]
        rw [hsum] at this
        simpa using this
    have lin : coboundary ρ n (fun x => (↑u⁻¹ : R) • prism R z f x) g =
        (↑u⁻¹ : R) • coboundary ρ n (prism R z f) g := by
      simp only [coboundary, map_smul, smul_add, smul_sum]
      congr 1
      exact sum_congr rfl fun j _ => smul_comm _ _ _
    rw [lin, key, ← hu, smul_smul, Units.inv_mul, one_smul]
end Formalism.CyclotomicNorms
