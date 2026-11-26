-- Prove2me | solution 1 for Eden.descending_radiusPairSpectrum_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:46.463433+00:00
-- url     : https://prove2.me/submissions/ed8baa35-11b5-4dbf-be30-ae7dcaac3139

import Definitions.Def_Eden_KaplanYorke
import Definitions.Def_Eden_SpectrumTable
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_antitone_eq_of_multiset_eq
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_descending_antitone
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_multiset_descending
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


section
noncomputable section
namespace Eden
private theorem descending_eq_of_antitone_and_multiset {f g : Fin 5 → ℝ}
    (hg : Antitone g) (hm : Finset.univ.val.map f = Finset.univ.val.map g) :
    descending f = g :=
  antitone_eq_of_multiset_eq (descending_antitone _) hg ((multiset_descending _).trans hm)
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] := by
  apply descending_eq_of_antitone_and_multiset
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp
    all_goals linarith
  · norm_num [radiusPairSpectrum, radialRate, tangentialRate]
end Eden
