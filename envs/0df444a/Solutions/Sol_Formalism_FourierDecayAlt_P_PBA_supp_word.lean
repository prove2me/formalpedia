-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.supp_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:50.090094+00:00
-- url     : https://prove2.me/submissions/dd1cc539-0033-42b7-b204-745fddcb3879

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_len_le_cnt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_cnt_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_admissible_of_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop)
    {g : C.Word S.f} (hg : g ∈ Fintype.piFinset (supp S A w U)) : S.AdmN g ∧ g.cnt ≤ n := by
  rw [Fintype.mem_piFinset] at hg
  have hv : ∀ v, D.AdmAt S v (g v) ∧ (g v).length ≤ n := by
    intro v
    have hgv := hg v
    unfold supp at hgv
    split_ifs at hgv with hA
    · exact hU v hA (g v) hgv
    · rw [Finset.mem_singleton] at hgv
      rw [hgv]
      exact ⟨Exists.intro w rfl, (len_le_cnt S w.1 v).trans hw⟩
  have hc : g.cnt ≤ n := cnt_le S (fun v => (hv v).2)
  exact ⟨And.intro (admissible_of_places S (fun v => (hv v).1)) (hc.trans hn), hc⟩
end Formalism.FourierDecayAlt.P.PBA
