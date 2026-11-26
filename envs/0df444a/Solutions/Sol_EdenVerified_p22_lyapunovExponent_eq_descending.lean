-- Prove2me | solution 1 for EdenVerified.p22_lyapunovExponent_eq_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:32:25.371883+00:00
-- url     : https://prove2.me/submissions/68cffcc2-aba3-42df-9e5f-dcbe3e5eaa70

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_lyapunovExponent_eq_descending


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    lyapunovExponent c p i = descending (factorExponents c p) i :=
  @Eden.lyapunovExponent_eq_descending
end EdenVerified
