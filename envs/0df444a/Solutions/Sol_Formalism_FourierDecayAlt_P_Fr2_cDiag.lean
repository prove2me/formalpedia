-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.cDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.149136+00:00
-- url     : https://prove2.me/submissions/3daed973-e529-4d58-8302-ff1d5f7a096e

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_ins_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr2_ins_sc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution : CDiag := by
  intro A S _ _ _ _ _ _ r L st P κ x0 hx hxi w
  have km : ∀ f g : P → ℂ, κ f * κ g = κ (fun ρ => f ρ * g ρ) := fun f g => (map_mul κ f g).symm
  have kc : ∀ c : ℂ, algebraMap ℂ A c = κ (fun _ => c) := fun c => (AlgHom.commutes κ c).symm
  have ks : ∀ (c : ℂ) (f : P → ℂ), c • κ f = κ (fun ρ => c * f ρ) := fun c f => (map_smul κ c f).symm
  have k1 : (1 : A) = κ (fun _ => 1) := (map_one κ).symm
  induction w with
  | nil =>
    refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
    · simp [ofWord, Start.frame, io, xs, hx, Matrix.scalar_apply]
    · simp [ofWord, Start.frame, io, xs, hxi, Matrix.scalar_apply]
    · simp only [ofWord, Start.frame, cs, ← k1, Matrix.diagonal_one]
  | cons l w ih =>
    obtain ⟨ihx, ihxi, ihc⟩ := ih
    have hq : (ofWord L st w).q = qw st.q w := by
      clear ihx ihxi ihc
      induction w with
      | nil => rfl
      | cons l' w ih' =>
        by_cases hl : l'.plus
        · funext Y; simp [ofWord, hl, FrameData.plus, qw, ih']
        · funext Y; simp [ofWord, hl, FrameData.minus, qw, ih']
    by_cases hp : l.plus
    · refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]
    · have hp' : l.plus = false := by simpa using hp
      refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]
end Formalism.FourierDecayAlt.P.Fr2
