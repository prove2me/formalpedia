-- Prove2me | solution 1 for Formalism.GM.FockB.step_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:00.809896+00:00
-- url     : https://prove2.me/submissions/e99a24f1-1883-4206-a49f-7d0dbec7e181

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_tieEh_pow_apply
import Theorems.Thm_Formalism_GM_F_pow_E_pow
import Theorems.Thm_Formalism_GM_ProjS_eig_P
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
import Theorems.Thm_Formalism_GM_ProjS_fh_P
import Theorems.Thm_Formalism_GM_ProjS_fockK_smul_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow
import Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow_right
import Theorems.Thm_Formalism_GM_ProjS_fockK_zero_left
import Theorems.Thm_Formalism_GM_ProjS_tieEh_eq
import Theorems.Thm_Formalism_GM_ProjS_tieP_eq
import Theorems.Thm_Formalism_GM_ProjS_tv_e
import Theorems.Thm_Formalism_GM_ProjS_tv_w
import Theorems.Thm_Formalism_GM_ProjS_tv_we


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.FockB
theorem _root_.solution [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n o' n' z : ℕ}
    {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o' n' y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    {j j' : ℕ} (hjj : j ≠ j') :
    M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j' * M.tieP w e zv sv o' n' z y') = 0 := by
  have hFP := ProjS.fh_P (z := z) hv hr hy hz
  have hFP' := ProjS.fh_P (z := z) hv hr hy' hz'
  have hE := ProjS.eig_P (z := z) hv hy' hz' (fun l => ((-1 : k) ^ l) / (((l.factorial : k) ^ 2) *
    ((o' + n' + r + z - 1).choose l : k)))
  rw [← ProjS.tieP_eq, ProjS.eulL_apply, ProjS.eulL_apply] at hE
  have key := Formalism.GM.F_pow_E_pow (ProjS.tv_w hv) (ProjS.tv_e hv) (ProjS.tv_we hv) (M.tieP w e zv sv o' n' z y')
    (o' + z) n' (o' + z + n' + r) hE.1 hE.2 hFP' (by omega) j j'
  rw [← tieEh_pow_apply, ← tieEh_pow_apply, ProjS.tieEh_eq, ProjS.fockK_tieE_pow, key, ProjS.fockK_smul_right]
  rcases Nat.lt_or_gt_of_ne hjj with hlt | hgt
  · have hd : j' - j = (j' - j - 1) + 1 := by omega
    rw [ProjS.fockK_tieE_pow_right, hd, pow_succ, Module.End.mul_apply, hFP, map_zero, ProjS.fockK_zero_left]
    simp
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hgt]
    simp
end Formalism.GM.FockB
