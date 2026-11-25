-- Prove2me | solution 1 for Formalism.GM.ProjS.fh_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:26.148726+00:00
-- url     : https://prove2.me/submissions/8aa4a64e-c26c-4707-ab6d-d8c2b588cb7f

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_F_E_pow_comm
import Theorems.Thm_Formalism_GM_ProjS_tv_w
import Theorems.Thm_Formalism_GM_ProjS_tv_e
import Theorems.Thm_Formalism_GM_ProjS_tv_we
import Theorems.Thm_Formalism_GM_ProjS_Fh_v
import Theorems.Thm_Formalism_GM_ProjS_eig_v
import Theorems.Thm_Formalism_GM_ProjS_v_top
import Theorems.Thm_Formalism_GM_ProjS_coef_cancel
import Theorems.Thm_Formalism_GM_ProjS_tieP_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
section
variable {s : ℕ} {w e : Fin s → σ}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
section
variable {o n z : ℕ} {y : MvPolynomial σ k}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
private theorem sum_range_smul_add_smul_eq_zero_of_recurrence {M : Type} [AddCommGroup M] [Module k M] (c d : ℕ → k) (F : ℕ → M) (o : ℕ)
    (hF : F o = 0) (hc : ∀ j < o, c j + c (j + 1) * d j = 0) :
    ∑ j ∈ range o, c (j + 1) • (F (j + 1) + d j • F j) + c 0 • F 0 = 0 := by
  have h1 : ∑ j ∈ range o, c (j + 1) • F (j + 1) + c 0 • F 0 = ∑ j ∈ range o, c j • F j := by
    rw [← Finset.sum_range_succ' (fun j => c j • F j), Finset.sum_range_succ, hF, smul_zero, add_zero]
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  rw [add_right_comm, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [← add_smul, hc j (Finset.mem_range.mp hj), zero_smul]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) (M.tieP w e zv sv o n z y) = 0 := by
  have hw' := tv_w hv
  have he' := tv_e hv
  have hd := tv_we hv
  have hT0 : Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)
      ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ 0) (X zv ^ z * y))) =
      (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ 0) ((Formalism.GM.tieF w e ^ (0 + 1)) (X zv ^ z * y)) := by
    have h0 := Fh_v (z := z) hv hz 0
    simpa using h0
  have hTs : ∀ j : ℕ, Formalism.GM.tieF (k := k) (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e)
      ((Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y))) =
      (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ (j + 1)) ((Formalism.GM.tieF w e ^ (j + 1 + 1)) (X zv ^ z * y)) +
      (((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
        ((r + 1 : ℕ) : k) + j)) •
        (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ j) ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y)) := by
    intro j
    have h1 := eig_v (z := z) hv hy hz (j + 1)
    rw [F_E_pow_comm hw' he' hd _ _ _ h1.1 h1.2.1 j, Fh_v (z := z) hv hz (j + 1)]
  have hF : (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ o)
      ((Formalism.GM.tieF w e ^ (o + 1)) (X zv ^ z * y)) = 0 := by
    rw [v_top hv hy hz, map_zero]
  rw [tieP_eq, map_sum, Finset.sum_range_succ']
  simp only [map_smul, hTs, hT0]
  exact sum_range_smul_add_smul_eq_zero_of_recurrence
    (fun l => ((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k)))
    (fun j => ((j : k) + 1) * (((o + z : ℕ) : k) - ((j + 1 : ℕ) : k) + ((n : k) - ((j + 1 : ℕ) : k)) +
        ((r + 1 : ℕ) : k) + j))
    (fun j => (Formalism.GM.tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ j)
      ((Formalism.GM.tieF w e ^ (j + 1)) (X zv ^ z * y))) o hF
    (fun j hj => coef_cancel o n r z j hr hj)
end Formalism.GM.ProjS
