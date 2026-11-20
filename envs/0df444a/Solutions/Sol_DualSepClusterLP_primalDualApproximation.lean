-- Prove2me | solution 1 for DualSepClusterLP.primalDualApproximation
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:08:27.727737+00:00
-- url     : https://prove2.me/submissions/e00ffe67-f713-41a4-860e-b2a3b899ee34

import Theorems.Thm_DualSepClusterLP_approximateSeparation
import Theorems.Thm_DualSepClusterLP_projectedCutSearchMachine
import Theorems.Thm_DualSepClusterLP_projectedCutSearchGuarantees

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b D d : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n), ∃ (L : SparseWeights n) (q : Fin n → ℚ),
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((graphInput t G).map M.inputAlphabet.symm)
          (some ((roundingInput G L ++ pricesBits q).map M.outputAlphabet.symm))
          (2 ^ (A * (t+1)^a) * (n+1)^b)) ∧
        ValidSupport L ∧ L.length ≤ D * (n+1)^d ∧
        DualFeasible G (fun i => (q i : ℝ)) ∧
        let opt : ℝ := sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v}
        let factor : ℝ := 1 + 1 / ((t : ℝ) + 1)
        opt ≤ factor * ∑ i : Fin n, (q i : ℝ) ∧
          primalValue G (fun S => (weightAt L S : ℝ)) ≤ factor * opt := by
  classical
  obtain ⟨M,A,a,b,hfin,oracle⟩ := approximateSeparation
  let O : CutRecovery.OracleFamily := fun u n G q => (oracle u n G q).choose
  have runs : CutRecovery.oracleRuns O M A a b := fun u n G q => (oracle u n G q).choose_spec.1
  have good (t n : ℕ) (G : Graph n) :
      CutRecovery.goodOracle t G (O (CutRecovery.scaleIndex t-1) n G) := by
    intro q
    let k := CutRecovery.scaleIndex t
    have hk : k-1+1=k := by dsimp [k,CutRecovery.scaleIndex]; omega
    have he : ((k-1:ℕ):ℝ)+1 = k := by exact_mod_cast hk
    have h := (oracle (k-1) n G q).choose_spec.2
    change match O (k-1) n G q with
      | some S => _
      | none => _ at h ⊢
    cases hr : O (k-1) n G q with
    | some S => simpa only [hr] using h
    | none =>
      rw [hr] at h
      simpa only [he,CutRecovery.tolerance,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  obtain ⟨P,B,c,d,hfinite,hP⟩ := projectedCutSearchMachine M A a b hfin O runs good
  refine ⟨P,B,c,d,257,9,hfinite,?_⟩
  intro t n G
  have hw := hP t n G
  have hg := projectedCutSearchGuarantees G t _ (good t n G)
  generalize hr : CutRecovery.solve G t (O (CutRecovery.scaleIndex t-1) n G) = answer at hw hg
  rcases answer with ⟨L,q⟩
  obtain ⟨J,hJ,hlen,heq,run⟩ := hw
  obtain ⟨_,_,hq,hlo,hhi⟩ := hg
  exact ⟨J,q,run,hJ,hlen,hq,hlo,heq.trans_le hhi⟩
