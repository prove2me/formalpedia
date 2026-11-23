-- Prove2me | solution 1 for CritWinSpin.p6b_6_3_tm_impl
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:25.032422+00:00
-- url     : https://prove2.me/submissions/fbdb429f-e72c-48df-a235-11f57cb08308
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
import Theorems.Thm_CritWinSpin_p6b_6_3_lift_tm
import Theorems.Thm_CritWinSpin_p6b_6_3_slot_tm

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

theorem p6b_6_3_tm_impl_assembled (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ (liftF : Str → Str) (slotM : PPT) (n₂ : ℕ) (û_fn : ℕ → ℚ),
        CookPvsNP.PolyTimeComputable liftF ∧
        (∀ n : ℕ, n₂ ≤ n → IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) (û_fn n)) ∧
        ∀ (n : ℕ) (H : Inst n), n₂ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          liftF (encInst H) =
            tupleCode [encInst (liftInst S p Ac Cc H (û_fn n)), encRat (û_fn n)] ∧
          ∀ (û : ℚ), IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û →
            ∀ y : BinCfg n,
              IsDistribution (slotKernel S p Cc slotM H û y) ∧
              ∃ (nuT aT : Config S (Fin n × Fin (cloudSize p Cc n)) → ℝ),
                (∀ σ, 0 ≤ nuT σ) ∧ ∑ σ, nuT σ = 1 ∧ (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) ∧
                (∀ σ, slotKernel S p Cc slotM H û y (some σ) = nuT σ * aT σ) ∧
                (∀ σ, 0 < slotKernel S p Cc slotM H û y (some σ) →
                  0 < idealSlot S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ))
                    (castM H.1) (castV H.2) (û : ℝ) y (some σ)) ∧
                ∑ σ : Config S (Fin n × Fin (cloudSize p Cc n)),
                  |nuT σ - nuProd S (((tauQ S + thetaQ p Ac Cc n : ℚ) : ℝ)) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2)) ∧
                (∀ σ, 0 < nuT σ →
                  |aT σ - ay (castM H.1) (castV H.2) (û : ℝ) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2))) := by
  intro w ε Ac Cc hw hε hεd hpar
  obtain ⟨liftF, û_fn, n₂, hlift_poly, hû, hlift⟩ :=
    p6b_6_3_lift_tm S p hS hp w ε Ac Cc hw hε hεd hpar
  obtain ⟨slotM, hslot⟩ := p6b_6_3_slot_tm S p hS hp w ε Ac Cc hw hε hεd hpar
  refine ⟨liftF, slotM, n₂, û_fn, hlift_poly, hû, ?_⟩
  intro n H hn hsymm hdiag hwidth
  exact ⟨hlift n H hn hsymm hdiag hwidth, hslot n H hsymm hdiag hwidth⟩

end CritWinSpin

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

theorem solution (S : CritWinSpin.SpinLaw) (p : ℕ) (hS : CritWinSpin.IsGHS S)
    (hp : CritWinSpin.IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < CritWinSpin.dExp p →
      CritWinSpin.GadgetParams p w ε Ac Cc →
      ∃ (liftF : Str → Str) (slotM : PPT) (n₂ : ℕ) (û_fn : ℕ → ℚ),
        CookPvsNP.PolyTimeComputable liftF ∧
        (∀ n : ℕ, n₂ ≤ n → CritWinSpin.IsUhat S ((CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)
          (CritWinSpin.cloudSize p Cc n) (û_fn n)) ∧
        ∀ (n : ℕ) (H : CritWinSpin.Inst n), n₂ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
          CritWinSpin.width (CritWinSpin.castM H.1) (CritWinSpin.castV H.2) ≤ (n : ℝ) ^ w →
          liftF (CritWinSpin.encInst H) =
            tupleCode [CritWinSpin.encInst (CritWinSpin.liftInst S p Ac Cc H (û_fn n)),
              encRat (û_fn n)] ∧
          ∀ (û : ℚ), CritWinSpin.IsUhat S ((CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)
              (CritWinSpin.cloudSize p Cc n) û →
            ∀ y : CritWinSpin.BinCfg n,
              IsDistribution (CritWinSpin.slotKernel S p Cc slotM H û y) ∧
              ∃ (nuT aT : CritWinSpin.Config S (Fin n × Fin (CritWinSpin.cloudSize p Cc n)) → ℝ),
                (∀ σ, 0 ≤ nuT σ) ∧ ∑ σ, nuT σ = 1 ∧ (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) ∧
                (∀ σ, CritWinSpin.slotKernel S p Cc slotM H û y (some σ) = nuT σ * aT σ) ∧
                (∀ σ, 0 < CritWinSpin.slotKernel S p Cc slotM H û y (some σ) →
                  0 < CritWinSpin.idealSlot S (((CritWinSpin.tauQ S +
                      CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ))
                    (CritWinSpin.castM H.1) (CritWinSpin.castV H.2) (û : ℝ) y (some σ)) ∧
                ∑ σ : CritWinSpin.Config S (Fin n × Fin (CritWinSpin.cloudSize p Cc n)),
                  |nuT σ - CritWinSpin.nuProd S
                    (((CritWinSpin.tauQ S + CritWinSpin.thetaQ p Ac Cc n : ℚ) : ℝ)) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2)) ∧
                (∀ σ, 0 < nuT σ →
                  |aT σ - CritWinSpin.ay (CritWinSpin.castM H.1) (CritWinSpin.castV H.2)
                      (û : ℝ) y σ| ≤
                    (1 / 2 : ℝ) * Real.exp (-(2 * (n : ℝ) ^ 2))) :=
  CritWinSpin.p6b_6_3_tm_impl_assembled S p hS hp
