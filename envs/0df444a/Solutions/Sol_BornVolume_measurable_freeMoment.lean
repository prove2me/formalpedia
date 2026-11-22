-- Prove2me | solution 1 for BornVolume.measurable_freeMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:57.876841+00:00
-- url     : https://prove2.me/submissions/9423cca4-4259-43cc-8ff2-4a836248fb4d

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
public import Theorems.Thm_BornVolume_momentMap_measurable


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    Measurable (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) :=
  measurable_pi_iff.mpr fun k => momentMap_measurable (Fin.castSucc k)
end BornVolume
