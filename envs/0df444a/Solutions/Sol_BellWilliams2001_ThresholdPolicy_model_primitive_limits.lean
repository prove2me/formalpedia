-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.model_primitive_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:08:49.480593+00:00
-- url     : https://prove2.me/submissions/3ba6dd5f-28b5-49c0-b0d3-9cee1b215a42

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_joint_centered_renewal_limits
import Theorems.Thm_ManyServerQED_Scheduling_independent_disjoint_groups_of_primitive_fields
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy ManyServerQED.Scheduling
open scoped ENNReal NNReal

private theorem rate_clock (V : ℕ → ℝ) (a : ℝ) (ha : 0 < a) (s : ℝ) :
    renewalCount (partialSum (fun j => V j/a)) s =
      renewalCount (fun j => ∑ l ∈ Finset.range j, V (l+1)) (a*s) := by
  have hsum (j : ℕ) : (∑ l ∈ Finset.range j, V (l+1)) = partialSum V j := by
    unfold partialSum
    rw [show Finset.Icc 1 j = Finset.Ico 1 (j+1) from by ext; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel,add_comm]
  have h (j : ℕ) : partialSum (fun j => V j/a) j = (∑ l ∈ Finset.range j, V (l+1))/a := by
    rw [hsum]
    simp [partialSum,Finset.sum_div]
  simp only [renewalCount,h,div_le_iff₀ ha,mul_comm a s]

set_option maxHeartbeats 2500000 in
theorem solution {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : SystemSequence Ω) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin 5 → ℝ≥0 → Ω' → ℝ) (hB : ∀ i, IsBrownianReal (B i) P')
    (hBc : ∀ i ω, Continuous (fun t => B i t ω))
    (hIndB : iIndepFun (fun i ω t => B i t ω) P') :
    letI := M.isProb
    let X (n : ℕ) (ω : Ω) (t : ℝ) := Fin.append (M.Ahat (φ n) ω t) (M.Shat (φ n) ω t)
    let Z (ω : Ω') (t : ℝ) (i : Fin 5) :=
      (Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
        (fun j => Real.sqrt (M.mu j*M.betaSq j))) i * B i t.toNNReal ω
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => M.P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let V (i : Fin 5) (n : ℕ) := Fin.append (fun k => M.uC k (n+1)) (fun j => M.vC j (n+1)) i
  let aN (n : ℕ) := Fin.append (M.lamR (φ n)) (M.muR (φ n))
  let a := Fin.append M.lam M.mu
  let τ : (Fin 5 × ℕ) ≃ ((Fin 2 × ℕ) ⊕ (Fin 3 × ℕ)) :=
    (Equiv.prodCongr (finSumFinEquiv (m := 2) (n := 3)).symm (Equiv.refl ℕ)).trans (Equiv.sumProdDistrib (Fin 2) (Fin 3) ℕ)
  have hτ (i : Fin 5) (j : ℕ) : (Sum.elim
      (fun q : Fin 2 × ℕ => M.uC q.1 (q.2+1))
      (fun q : Fin 3 × ℕ => M.vC q.1 (q.2+1))) (τ (i,j)) = V i j := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k
    · have he : V ((finSumFinEquiv (m := 2) (n := 3)) (.inl k)) j = M.uC k (j+1) := by
        rw [finSumFinEquiv_apply_left]
        exact Fin.append_left _ _ _
      rw [he]
      simp [τ]
    · have he : V ((finSumFinEquiv (m := 2) (n := 3)) (.inr k)) j = M.vC k (j+1) := by
        rw [finSumFinEquiv_apply_right]
        exact Fin.append_right _ _ _
      rw [he]
      simp [τ]
  have hInd : iIndepFun (fun ij : Fin 5 × ℕ => V ij.1 ij.2) M.P := by
    have h := M.indep.precomp τ.injective
    simpa only [hτ] using h
  have hm (i : Fin 5) (j : ℕ) : Measurable (V i j) := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · exact M.uC_meas _ _
    · exact M.vC_meas _ _
  have hSeq : iIndepFun (fun i ω j => V i j ω) M.P := by
    let H (ij : Fin 5 × ℕ) := MeasurableSpace.comap (V ij.1 ij.2) inferInstance
    let D (i : Fin 5) : Set (Fin 5 × ℕ) := {ij | ij.1 = i}
    have hD : Pairwise (fun i j => Disjoint (D i) (D j)) := by
      intro i j hij
      exact Set.disjoint_left.2 fun _ hi hj => hij (hi.symm.trans hj)
    have h := independent_disjoint_groups_of_primitive_fields H
      (fun ij => (hm ij.1 ij.2).comap_le) ((iIndepFun_iff_iIndep _ _ _).1 hInd) D hD
    apply (iIndepFun_iff_iIndep _ _ _).2
    refine iIndep_of_iIndep_of_le h fun i => ?_
    apply measurable_iff_comap_le.1
    letI : MeasurableSpace Ω := ⨆ j ∈ D i, H j
    exact measurable_pi_lambda _ (fun j => measurable_iff_comap_le.2
      (le_iSup₂_of_le (i,j) (show (i,j) ∈ D i from rfl) le_rfl))
  have hId (i : Fin 5) (j : ℕ) : IdentDistrib (V i j) (V i 0) M.P M.P := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right,Nat.zero_add]
    · exact M.uC_ident k (j+1) (by omega)
    · exact M.vC_ident k (j+1) (by omega)
  have hLp (i : Fin 5) : MemLp (V i 0) 2 M.P := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right,Nat.zero_add]
    · exact M.uC_memLp k
    · exact M.vC_memLp k
  have hMean (i : Fin 5) : ∫ ω, V i 0 ω ∂M.P = 1 := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right,Nat.zero_add]
    · exact M.uC_mean k
    · exact M.vC_mean k
  have hp (i : Fin 5) (j : ℕ) (ω : Ω) : 0 < V i j ω := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · exact M.uC_pos k (j+1) ω (by omega)
    · exact M.vC_pos k (j+1) ω (by omega)
  have haN (n : ℕ) (i : Fin 5) : 0 ≤ aN n i := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [aN,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · exact (M.lamR_pos _ _).le
    · exact (M.muR_pos _ _).le
  have ha (i : Fin 5) : 0 < a i := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [a,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · exact M.lam_pos k
    · exact M.mu_pos k
  have hLim (i : Fin 5) : Tendsto (fun n => aN n i) atTop (𝓝 (a i)) := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [a,aN,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · exact (M.a31_iii k).comp hφ
    · exact (M.a31_iv k).comp hφ
  have h := joint_centered_renewal_limits V hm (fun i => hInd.precomp
      (show Function.Injective (fun j => (i,j)) from fun _ _ h => congrArg Prod.snd h))
    hId hLp hMean hp hSeq (M.r ∘ φ) (fun n => M.r_ge (φ n)) (M.r_tendsto.comp hφ)
    aN haN a ha hLim B hB hBc hIndB
  have hX (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin 5) :
    (((renewalCount (fun j => ∑ l ∈ Finset.range j, V i l ω) (aN n i*(M.r (φ n)^2*t))).toNat:ℝ)
      - aN n i*(M.r (φ n)^2*t)) / M.r (φ n) =
    (Fin.append (M.Ahat (φ n) ω t) (M.Shat (φ n) ω t)) i := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,aN,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right]
    · rw [←rate_clock (fun j => M.uC k j ω) _ (M.lamR_pos (φ n) k)]
      rfl
    · rw [←rate_clock (fun j => M.vC k j ω) _ (M.muR_pos (φ n) k)]
      rfl
  have hZ (i : Fin 5) : Real.sqrt (a i*variance (V i 0) M.P) =
    (Fin.append (fun k => Real.sqrt (M.lam k*M.alphaSq k))
      (fun j => Real.sqrt (M.mu j*M.betaSq j))) i := by
    obtain ⟨i,rfl⟩ := (finSumFinEquiv (m := 2) (n := 3)).surjective i
    rcases i with k | k <;> simp only [V,a,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
      Fin.append_left,Fin.append_right,Nat.zero_add] <;> rfl
  simpa only [Function.comp_def,hX,hZ] using h
