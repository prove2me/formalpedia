-- Prove2me | solution 1 for Eden.lyapunovExponent_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:49.070003+00:00
-- url     : https://prove2.me/submissions/585bdaeb-babc-4772-95b7-7c07eb1cbc67

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
import Theorems.Thm_Eden_lyapunovExponent_eq_descending
import Theorems.Thm_Eden_descending_antitone


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) := by
  intro i j hij
  rw [lyapunovExponent_eq_descending, lyapunovExponent_eq_descending]
  exact descending_antitone (factorExponents c p) hij
end Eden
