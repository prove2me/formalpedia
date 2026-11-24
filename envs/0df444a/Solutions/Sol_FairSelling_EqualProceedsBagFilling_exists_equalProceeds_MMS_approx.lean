-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMS_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:40.117503+00:00
-- url     : https://prove2.me/submissions/b0165318-2a38-4ea8-bb88-d10567ccf939

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_TPS_approx
import Theorems.Thm_FairSelling_MMS_le_TPS


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [Fintype G] [DecidableEq G]
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, MMS n (v i) p / n ≤ util (v i) o i := by
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_TPS_approx v p hn hv hp
  refine ⟨o, hvalid, hep, fun i => le_trans ?_ (hsat i)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  gcongr
  exact MMS_le_TPS (v i) p hn (hv i) hp
end FairSelling.EqualProceedsBagFilling
