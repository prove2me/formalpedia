-- Prove2me | solution 1 for ClusterSim.EdgeCut.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:11:56.548971+00:00
-- url     : https://prove2.me/submissions/16914b74-d19b-4216-b2f2-c6e3c6b5a1c5

import Definitions.Def_ClusterSim_EdgeCut_Estimator
import Theorems.Thm_ClusterSim_EdgeCut_eqs_35_36
import Theorems.Thm_ClusterSim_EdgeCut_hoeffding_inequality
import Theorems.Thm_ClusterSim_EdgeCut_pieces

open ClusterSim.EdgeCut MeasureTheory

theorem solution {G : TensorNetwork} {r K d : ℕ} (P : Clustering G r) (hP : P.IsClustered K d)
    (run : (P.Ecut → Fin 8) → Measure ℝ) [∀ s, IsProbabilityMeasure (run s)]
    (hrange : ∀ s, ∀ᵐ t ∂(run s), t ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ s, ((∫ t, t ∂(run s) : ℝ) : ℂ) = value (cut G P.Ecut s))
    {ε : ℝ} (hε : 0 < ε) :
    (2 / 3 : ENNReal) ≤
        Measure.pi (fun _ : Fin (numSamples K ε) => sampleLaw P run)
          {x | ‖((average x : ℝ) : ℂ) - value G‖ < ε} ∧
      ∀ s : P.Ecut → Fin 8,
        (P.cutClustering s).Ecut = ∅ ∧ ∀ i, (P.cutClustering s).qubits i ≤ d := by
  refine ⟨?_, fun s => pieces P hP s⟩
  obtain ⟨hprob, hbound, hexp⟩ := eqs_35_36 P run hrange hmean
  have : IsProbabilityMeasure (sampleLaw P run) := hprob
  have hK : P.Ecut.card = K := hP.1
  set a : ℝ := (2 : ℝ) ^ (2 * K)
  have ha : 0 < a := by positivity
  have hbound' : ∀ᵐ x ∂(sampleLaw P run), |x| ≤ a := by
    simpa only [a, hK] using hbound
  have ha2 : a ^ 2 = (2 : ℝ) ^ (4 * K) := by
    dsimp [a]
    rw [← pow_mul]
    ring_nf
  have hpos_arg : 0 < 4 * (2 : ℝ) ^ (4 * K) / ε ^ 2 := by positivity
  have hN : 0 < numSamples K ε := Nat.ceil_pos.mpr hpos_arg
  have hNa : 4 * a ^ 2 / ε ^ 2 ≤ (numSamples K ε : ℝ) := by
    rw [ha2]
    exact Nat.le_ceil _
  obtain ⟨hhoeff1, hhoeff2⟩ :=
    hoeffding_inequality (sampleLaw P run) ha hε hbound' (numSamples K ε) hN
  have h23_real : (2 / 3 : ℝ) <
      1 - 2 * Real.exp (-(numSamples K ε * ε ^ 2) / (2 * a ^ 2)) :=
    hhoeff2 hNa
  have h23_enn : (2 / 3 : ENNReal) = ENNReal.ofReal (2 / 3 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  have hset : {x : Fin (numSamples K ε) → ℝ |
        |(∑ i, x i) / (numSamples K ε : ℝ) - ∫ t, t ∂(sampleLaw P run)| < ε} =
      {x : Fin (numSamples K ε) → ℝ | ‖((average x : ℝ) : ℂ) - value G‖ < ε} := by
    ext x
    simp only [Set.mem_setOf_eq, ClusterSim.EdgeCut.average, ← hexp, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [h23_enn, ← hset]
  exact le_trans (ENNReal.ofReal_le_ofReal (le_of_lt h23_real)) hhoeff1
