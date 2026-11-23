-- Prove2me | solution 1 for CritWinSpin.p6b_6_3_slot_tm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:50:24.124633+00:00
-- url     : https://prove2.me/submissions/8bc9fd12-9e88-47df-9062-61f0d76841f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CritWinSpin_p6b_6_3_proposal_tm
import Theorems.Thm_CritWinSpin_p6b_6_3_rejection_tm
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
set_option autoImplicit false

theorem solution (S : CritWinSpin.SpinLaw) (p : ℕ) (hS : CritWinSpin.IsGHS S)
    (hp : CritWinSpin.IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < CritWinSpin.dExp p →
      CritWinSpin.GadgetParams p w ε Ac Cc →
      ∃ slotM : PPT,
        ∀ (n : ℕ) (H : CritWinSpin.Inst n), H.1.IsSymm → (∀ i, H.1 i i = 0) →
          CritWinSpin.width (CritWinSpin.castM H.1) (CritWinSpin.castV H.2) ≤ (n : ℝ) ^ w →
          ∀ (û : ℚ), CritWinSpin.IsUhat S ((CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)
              (CritWinSpin.cloudSize p Cc n) û →
            ∀ y : CritWinSpin.BinCfg n,
              IsDistribution (CritWinSpin.slotKernel S p Cc slotM H û y) ∧
              ∃ (nuT aT : CritWinSpin.Config S
                  (Fin n × Fin (CritWinSpin.cloudSize p Cc n)) → ℝ),
                (∀ σ, 0 ≤ nuT σ) ∧ ∑ σ, nuT σ = 1 ∧ (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) ∧
                (∀ σ, CritWinSpin.slotKernel S p Cc slotM H û y (some σ) = nuT σ * aT σ) ∧
                (∀ σ, 0 < CritWinSpin.slotKernel S p Cc slotM H û y (some σ) →
                  0 < CritWinSpin.idealSlot S
                    (((CritWinSpin.tauQ S + CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ))
                    (CritWinSpin.castM H.1) (CritWinSpin.castV H.2) (û : ℝ) y (some σ)) ∧
                ∑ σ : CritWinSpin.Config S (Fin n × Fin (CritWinSpin.cloudSize p Cc n)),
                  |nuT σ - CritWinSpin.nuProd S
                    (((CritWinSpin.tauQ S + CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2)) ∧
                (∀ σ, 0 < nuT σ →
                  |aT σ - CritWinSpin.ay (CritWinSpin.castM H.1) (CritWinSpin.castV H.2)
                      (û : ℝ) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2))) := by
  intro w ε Ac Cc hw hε hεd hpar
  obtain ⟨propM, hprop⟩ :=
    CritWinSpin.p6b_6_3_proposal_tm S p hS hp w ε Ac Cc hw hε hεd hpar
  obtain ⟨slotM, hreject⟩ := CritWinSpin.p6b_6_3_rejection_tm S p Cc propM
  refine ⟨slotM, ?_⟩
  intro n H hsymm hdiag hwidth û hû y
  obtain ⟨nuT, hnu0, hnusum, hproplaw, hnusupp, hnerr⟩ :=
    hprop n H hsymm hdiag hwidth û hû y
  obtain ⟨hdist, aT, ha, hfactor, hideal, haerr⟩ :=
    hreject n H û y (((CritWinSpin.tauQ S + CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)) nuT
      hproplaw hnu0 hnusum hnusupp
  exact ⟨hdist, nuT, aT, hnu0, hnusum, ha, hfactor, hideal, hnerr, haerr⟩
