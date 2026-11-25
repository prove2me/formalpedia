-- Prove2me | solution 1 for Formalism.MainNotions.J.int_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:33.176526+00:00
-- url     : https://prove2.me/submissions/0d3631ed-39ab-4092-9bd0-85eaff370218

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
import Theorems.Thm_Formalism_MainNotions_J_exists_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.J
open MvPowerSeries
section AlgebraTools
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]
private theorem hasSubst_of_finite_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {c : σ → MvPowerSeries τ R}
    (hc : ∀ s, constantCoeff (c s) = 0) : HasSubst c := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hc
end AlgebraTools
section Exp
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
end Exp
section Int
variable {ι κ : Type} {K : Type} [Field K]
private theorem finsum_mem_subring (O : Subring K) {α : Type} (F : α → K) (hF : ∀ x, F x ∈ O) :
    ∑ᶠ x, F x ∈ O := by
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    exact Subring.sum_mem O (fun x _ => hF x)
  · rw [finsum_of_infinite_support hfin]
    exact O.zero_mem
private theorem mem_range_map_subring_iff {σ : Type} (O : Subring K) (F : MvPowerSeries σ K) :
    F ∈ (MvPowerSeries.map (σ := σ) O.subtype).range ↔ ∀ n, coeff n F ∈ O := by
  constructor
  · intro hF n
    obtain ⟨F', rfl⟩ := RingHom.mem_range.mp hF
    rw [MvPowerSeries.coeff_map]
    exact (coeff n F').2
  · intro hF
    obtain ⟨F', hF'⟩ := exists_lift O F hF
    exact RingHom.mem_range.mpr ⟨F', hF'⟩
private theorem coeff_subst_mem_subring {σ τ : Type} (O : Subring K) (A : MvPowerSeries σ K)
    (hA : ∀ n, coeff n A ∈ O) (c : σ → MvPowerSeries τ K) (hc : HasSubst c)
    (hcO : ∀ i n, coeff n (c i) ∈ O) : ∀ n, coeff n (subst c A) ∈ O := by
  intro e
  rw [MvPowerSeries.coeff_subst hc]
  apply finsum_mem_subring
  intro d
  simp only [smul_eq_mul]
  refine O.mul_mem (hA d) ?_
  have hmem : (d.prod fun s k => c s ^ k) ∈ (MvPowerSeries.map (σ := τ) O.subtype).range := by
    simp only [Finsupp.prod]
    apply Subring.prod_mem
    intro s _
    exact Subring.pow_mem _ ((mem_range_map_subring_iff O (c s)).mpr (hcO s)) _
  exact (mem_range_map_subring_iff O _).mp hmem e
end Int
end Formalism.MainNotions.J
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K : Type} [Field K]
namespace Formalism.MainNotions.J
theorem _root_.solution [Finite ι] (O : Subring K) (A : MvPowerSeries ι K) (hA : ∀ n, coeff n A ∈ O)
    (c : ι → MvPowerSeries κ K) (hc0 : ∀ i, constantCoeff (c i) = 0) (hc : ∀ i n, coeff n (c i) ∈ O) :
    ∀ n, coeff n (subst c A) ∈ O := by
  exact coeff_subst_mem_subring O A hA c (hasSubst_of_finite_constantCoeff_eq_zero hc0) hc
end Formalism.MainNotions.J
