-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.topDensNonnegOfKappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:02.054527+00:00
-- url     : https://prove2.me/submissions/fb48102b-7dc9-47e7-a528-5972d30a3da3

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDensNonnegOfKappa
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_ofWord_c_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_act_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_pow_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P5_WordTransvectionCongruences_hsInner_zero_left
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_io
import Theorems.Thm_Formalism_FourierDecayAlt_P5_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_hsInner_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_cPos_true
import Theorems.Thm_Formalism_FourierDecayAlt_P_c_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_c_pos_truncated
import Theorems.Thm_Formalism_FourierDecayAlt_P_interlacing_sign
import Theorems.Thm_Formalism_FourierDecayAlt_P_q_positive_interlacing
import Theorems.Thm_Formalism_FourierDecayAlt_P_q_positive_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_types_interlace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
open WordTransvectionCongruences
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : TopDensNonnegOfKappa := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 K hD hl1 hlk hK
  obtain ⟨κ, hκx, hκxi, hκpos⟩ := hK
  obtain ⟨hPl, -, hAL, -, hq, -, -, -⟩ := hD
  intro w hw x _ c _ g

  let st' : Fr.Start (Pr (RadSp P.k P.r z z' π π')) :=
    { st with xi := fun Y => κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ }
  have hCD := (Formalism.FourierDecayAlt.P.c_diagonal (Pr (RadSp P.k P.r z z' π π')) S P.r L st' (M.Ty P) κ
    (fun ρ Y => M.x0 P l0 ρ Y) hκx (fun Y => rfl) w).2.2
  have hc : (Fr.ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [← ofWord_c_congr L st st' rfl rfl w, hCD]
    · rw [← hq]
    · intro l hl
      have h := hw.1.2.2.1 l hl
      exact ⟨(hκxi _ h.2.1).symm, (hκxi _ h.2.2.1).symm⟩

  have hpos : ∀ (e : Ix S) (ρ : M.Ty P), 0 < Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    intro e ρ
    have h := Formalism.FourierDecayAlt.P.c_pos_truncated Formalism.FourierDecayAlt.P.interlacing_sign Formalism.FourierDecayAlt.P.q_positive_interlacing
      Formalism.FourierDecayAlt.P.q_positive_shift Formalism.FourierDecayAlt.P.cPos_true S P.k P.u P.u' (M.rho P ρ) l0 P.T P.T' w hl1 hlk
      (Formalism.FourierDecayAlt.P.types_interlace P hPl.1 ρ) hPl.1.T_pos hPl.1.T'_pos hw.2.1 hw.2.2 e
    rw [Complex.lt_def]
    exact ⟨h.1, h.2.symm⟩
  unfold topDens
  refine Finset.sum_nonneg fun e _ => ?_
  have hd : (Fr.ofWord L st w).d L = io ((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N) *
      Matrix.diagonal fun e => κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e := by
    rw [Fr.FrameData.d, hc, Fr.wt, io, io, map_pow]
  rw [act_mul, hd, act_mul, act_io, act_diagonal]
  set Φ := act (Fr.ofWord L st w).F x e
  by_cases hp : (c, g) ∈ DomR P.k P.r z z'
  · have := pow_apply X L hAL (Fr.ofWord L st w).N ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ) (c, g) hp
    simp only at this
    rw [this, hsInner_smul_left]
    refine mul_nonneg ?_ (hκpos _ (hpos e) Φ c g)
    obtain ⟨-, -, hGG⟩ := hp
    have hre : fnVal P.k P.r z z' 0 g * fnVal P.k P.r z z' 2 g * fnVal P.k P.r z z' 5 g =
        ((Complex.normSq (zetaL P.k P.r z z' (Fin.last P.r) g) * (GGl P.k P.r z z' g)⁻¹ : ℝ) : ℂ) := by
      simp only [fnVal, Complex.ofReal_mul, Complex.ofReal_inv, ← Complex.mul_conj]
      rfl
    rw [hre, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (pow_nonneg (mul_nonneg (Complex.normSq_nonneg _) (inv_nonneg.mpr hGG.le)) _)
  · have h0 := ((((L.ζ * L.ζb * L.GGi) ^ (Fr.ofWord L st w).N).1
      ((κ fun ρ => Fr.cs (M.x0 P l0 ρ) (M.qC P) w e).1 Φ)).2).1 (c, g) hp
    simp only at h0
    rw [h0, hsInner_zero_left]
end Formalism.FourierDecayAlt.P5
