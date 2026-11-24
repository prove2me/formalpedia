-- Prove2me | solution 1 for Formalism.GM.M.Q_sat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:33.014633+00:00
-- url     : https://prove2.me/submissions/7f9702a0-c1d2-4dbf-8063-835ab8acf722

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_tensorSat
import Theorems.Thm_Formalism_GM_M_intPol_iff_isInt
import Theorems.Thm_P2M_Formalism_GM_M_intPol_monomial__c4f29bf6f8d7
import Theorems.Thm_Formalism_GM_M_xi_mono
import Theorems.Thm_Formalism_GM_M_chainEmb_inj
import Theorems.Thm_Formalism_GM_M_xiVar_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)
namespace Formalism.GM.M
theorem _root_.solution (j : Fin D.T.t → ℕ) (jp : ℕ) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp)) (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp) := by
  classical
  refine tensorSat (chainEmb N r D.T.t) (chainEmb_inj D) (Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr)
    (YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr) ?_ ?_ (XiPolZ p N r D.T.t (D.B - jp))
    (finsuppAntidiag (univ.image (xiVar N r D.T.t)) (D.B - jp)) ?_ ?_ ?_ (zmS D) Q hQ hint
  · intro y hy; exact (Submodule.mem_inf.mp hy).1
  · intro y hy hi
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_inf.mpr ⟨?_, (intPol_iff_isInt y).mpr hi⟩⟩
    exact (Submodule.mem_inf.mp hy).1
  · intro g hg m hm
    obtain ⟨h1, h2⟩ := xi_mono D hg hm
    rw [mem_finsuppAntidiag]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ h => xiVar_inj D h)]; exact h2
    · intro v hv
      obtain ⟨c, rfl⟩ := h1 v hv
      exact Finset.mem_image_of_mem _ (mem_univ c)
  · intro μ hμ
    rw [mem_finsuppAntidiag] at hμ
    refine Submodule.mem_inf.mpr ⟨?_, intPol_monomial' μ⟩
    rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff]
    intro m hm
    rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hm
    split_ifs at hm with h
    · subst h
      refine ⟨fun v hv => ?_, ?_⟩
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp (hμ.2 hv)
        exact ⟨c, rfl⟩
      · rw [← hμ.1, Finset.sum_image (fun a _ b _ h => xiVar_inj D h)]
    · exact absurd rfl hm
  · intro μ hμ x
    rw [mem_finsuppAntidiag] at hμ
    by_contra h
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp (hμ.2 (Finsupp.mem_support_iff.mpr h))
    obtain ⟨a, b⟩ := x
    simp [xiVar, chainEmb] at hc
    exact (Fin.castSucc_ne_last a) hc.1.symm
end Formalism.GM.M
