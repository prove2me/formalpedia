-- Prove2me | solution 1 for Formalism.GM.M.ss_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:15.183803+00:00
-- url     : https://prove2.me/submissions/ffc65824-16b9-4729-9887-d50d738ffccf

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_absSat
import Theorems.Thm_Formalism_GM_M_lv_inj
import Theorems.Thm_Formalism_GM_M_intPol_iff_isInt
import Theorems.Thm_Formalism_GM_M_topV
import Theorems.Thm_Formalism_GM_M_Q_of_top
import Theorems.Thm_Formalism_GM_M_pre_span_mem
import Theorems.Thm_Formalism_GM_M_SSZ_int
import Theorems.Thm_Formalism_GM_M_Q_sat

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
theorem _root_.solution (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])))
    (hi : x ∈ IntPol p (BVar N r D.T.t)) : x ∈ D.SSZ p (r := r) := by
  classical
  rw [BlockData.SSZ, Submodule.span_span_of_tower] at hx
  have hU : (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens p (r := r) j jp) =
      ⋃ (ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2}), D.gens p (r := r) ij.1.1 ij.1.2 := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, jp, h, hy⟩; exact ⟨⟨(j, jp), h⟩, hy⟩
    · rintro ⟨⟨⟨j, jp⟩, h⟩, hy⟩; exact ⟨j, jp, h, hy⟩
  rw [hU, Submodule.span_iUnion, Submodule.mem_iSup_iff_exists_finset] at hx
  obtain ⟨s, hs⟩ := hx
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨μ, hμ⟩ := hs
  rw [← hμ] at hi ⊢
  have key := absSat (scalS N r D.T.t)
    (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) (fun ij => lv ij.1.1 ij.1.2)
    (fun a b h => by obtain ⟨h1, h2⟩ := lv_inj h; exact Subtype.ext (Prod.ext h1 h2))
    (algebraMap ℤ_[p] ℚ_[p]).range.toAddSubgroup (D.SSZ p (r := r)).toAddSubgroup
    (fun L v hv => by obtain ⟨_, _, _, _, _, h1, _⟩ := topV D _ _ v hv; exact h1)
    (fun f hf m => (intPol_iff_isInt f).mp (SSZ_int D f hf) m)
    (fun L v hv htop => by
      obtain ⟨Q, hQ, rfl, hz⟩ := Q_of_top D _ _ v hv (fun c => c ∈ (algebraMap ℤ_[p] ℚ_[p]).range)
        (Subring.zero_mem _) htop
      exact pre_span_mem D _ _ L.2 Q (Q_sat D _ _ Q hQ hz))
    s (fun i => (μ i : MvPolynomial (BVar N r D.T.t) ℚ_[p])) (fun L _ => (μ L).2)
    (fun m => (intPol_iff_isInt _).mp hi m)
  exact key
end Formalism.GM.M
