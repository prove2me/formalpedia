-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMSEP_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:53.608801+00:00
-- url     : https://prove2.me/submissions/3514ee87-9032-4dfa-9d16-db7eb3c73088

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_MMS_approx
import Theorems.Thm_FairSelling_MMSEP_le_MMS


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
      ∀ i, MMSEP n (v i) p / n ≤ util (v i) o i := by
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_MMS_approx v p hn hv hp
  refine ⟨o, hvalid, hep, fun i => le_trans ?_ (hsat i)⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  gcongr
  exact MMSEP_le_MMS (v i) p hn (hv i) hp
end FairSelling.EqualProceedsBagFilling
