-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:35:35.218716+00:00
-- url     : https://prove2.me/submissions/873823dd-316f-47f0-b359-e2a69731b1c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_1
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_4_compl
import Theorems.Thm_ForkJoinCtrl_Tracking_eq_35

open MeasureTheory Filter Topology
open ForkJoinCtrl.Tracking
open scoped Pointwise

namespace FJP3

variable {N : Network}

def scaleVar (c : ℝ) (x : LPVar N) : LPVar N := ⟨fun j => c * x.y j, fun i j => c * x.q i j⟩

theorem feas_scale {c : ℝ} (hc : 0 ≤ c) {b : LPParam N} {x : LPVar N} (hx : LPFeasible N b x) :
    LPFeasible N (c • b) (scaleVar c x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun k => ?_, fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · simp only [scaleVar, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (h1 k) hc
  · simp only [scaleVar]
    rw [← mul_sub]; exact mul_nonneg hc (h2 i j hij)
  · simp only [scaleVar, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [← h3 i, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  · simp only [scaleVar]; exact mul_nonneg hc (h4 i j hij)
  · simp only [scaleVar]; rw [h5 i j hij, mul_zero]

theorem obj_scale (c : ℝ) (x : LPVar N) : LPObj N (scaleVar c x) = c * LPObj N x := by
  simp only [LPObj, scaleVar, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

theorem z_smul {c : ℝ} (hc : 0 < c) (b : LPParam N) : z N (c • b) = c * z N b := by
  have hset : LPObj N '' {x | LPFeasible N (c • b) x} = c • (LPObj N '' {x | LPFeasible N b x}) := by
    ext v
    simp only [Set.mem_image, Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨LPObj N (scaleVar c⁻¹ x), ⟨scaleVar c⁻¹ x, ?_, rfl⟩, ?_⟩
      · have := feas_scale (inv_nonneg.2 hc.le) hx
        rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      · rw [obj_scale, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨scaleVar c x, feas_scale hc.le hx, obj_scale c x⟩
  unfold z
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

theorem obj_nonneg (b : LPParam N) (x : LPVar N) (hf : LPFeasible N b x) : 0 ≤ LPObj N x := by
  unfold LPObj
  apply Finset.sum_nonneg
  intro j _
  obtain ⟨i, hi⟩ := N.exists_server j
  have h1 := hf.2.1 i j hi
  have h2 := hf.2.2.2.1 i j hi
  exact mul_nonneg (N.h_nonneg j) (by linarith)

/-- `z(b)` equals the convex objective (17a) at the `q`-part of a QP optimum -/
theorem z_eq_obj17 (b : LPParam N) (hb : b.Nonneg) (x : LPVar N) (hx : QPOpt N b x) :
    z N b = ∑ j, N.h j * N.jobMax j b.1 (fun i => x.q i j) := by
  have hbdd : BddBelow (LPObj N '' {x' | LPFeasible N b x'}) :=
    ⟨0, by rintro v ⟨x', hx', rfl⟩; exact obj_nonneg b x' hx'⟩
  have hle : z N b ≤ LPObj N x := csInf_le hbdd ⟨x, hx.1.1, rfl⟩
  have hge : LPObj N x ≤ z N b := hx.1.2
  have hleast : IsLeast (LPObj N '' {x' | LPFeasible N b x'}) (LPObj N x) := by
    refine ⟨⟨x, hx.1.1, rfl⟩, ?_⟩
    rintro v ⟨x', hx', rfl⟩
    exact hge.trans (csInf_le hbdd ⟨x', hx', rfl⟩)
  have := (ForkJoinCtrl.Tracking.lemma_1_part_1 N b hb x hx.1.1 hleast).2.2
  unfold Obj17 at this
  linarith

theorem jobMax_sub_le (j : Fin N.J) (qk : Fin N.K → ℝ) (qa qb : Fin N.I → ℝ) :
    |N.jobMax j qk qa - N.jobMax j qk qb| ≤ ∑ i ∈ N.Ij j, |qa i - qb i| := by
  have hD : 0 ≤ ∑ i ∈ N.Ij j, |qa i - qb i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have key : ∀ qa qb : Fin N.I → ℝ,
      N.jobMax j qk qa ≤ N.jobMax j qk qb + ∑ i ∈ N.Ij j, |qa i - qb i| := by
    intro qa qb
    have hD : 0 ≤ ∑ i ∈ N.Ij j, |qa i - qb i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    unfold Network.jobMax
    apply Finset.max'_le
    intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · have : c ≤ ((N.Kj j).image qk ∪ (N.Ij j).image qb).max'
          (Finset.Nonempty.mono Finset.subset_union_right ((N.Ij_nonempty j).image qb)) :=
        Finset.le_max' _ _ (Finset.mem_union_left _ hc)
      linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
      have h1 : qb i ≤ ((N.Kj j).image qk ∪ (N.Ij j).image qb).max'
          (Finset.Nonempty.mono Finset.subset_union_right ((N.Ij_nonempty j).image qb)) :=
        Finset.le_max' _ _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))
      have h2 : |qa i - qb i| ≤ ∑ i ∈ N.Ij j, |qa i - qb i| :=
        Finset.single_le_sum (f := fun i => |qa i - qb i|) (fun _ _ => abs_nonneg _) hi
      have h3 := le_abs_self (qa i - qb i)
      linarith
  have k1 := key qa qb
  have k2 := key qb qa
  have hs : ∑ i ∈ N.Ij j, |qb i - qa i| = ∑ i ∈ N.Ij j, |qa i - qb i| := by
    apply Finset.sum_congr rfl; intro i _; exact abs_sub_comm _ _
  rw [hs] at k2
  rw [abs_le]; constructor <;> linarith


section Run

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Model N Ω P} {r : ℕ}

theorem Nj_eq (X : Paths N Ω) {ω : Ω} (hω : X.IsAdmissibleAt M r ω) (j : Fin N.J) {u : ℝ}
    (hu : 0 ≤ u) :
    X.Nj j ω u = N.jobMax j (fun k => X.Qk k ω u) (fun i => X.Qij i j ω u) := by
  have h3 := hω.2.2.1
  have h4 := hω.2.2.2.1
  have h5 := hω.2.2.2.2.1 j u hu
  have h6 := hω.2.2.2.2.2.1 j u hu
  apply le_antisymm
  · rcases h6 with ⟨k, hk, hk0⟩ | ⟨i, hi, hi0⟩
    · rw [h5.1 k hk, hk0, add_zero]
      unfold Network.jobMax
      exact Finset.le_max' _ _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem (fun k => X.Qk k ω u) hk))
    · rw [h5.2 i hi, hi0, add_zero]
      unfold Network.jobMax
      exact Finset.le_max' _ _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun i => X.Qij i j ω u) hi))
  · unfold Network.jobMax
    apply Finset.max'_le
    intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      rw [h5.1 k hk]; linarith [(h3 k u hu).2]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
      have hij : N.P i j = true := by simpa [Network.Ij] using hi
      rw [h5.2 i hi]; linarith [(h4 i j u hij hu).2]

theorem b_nonneg (X : Paths N Ω) {ω : Ω} (hω : X.IsAdmissibleAt M r ω) {u : ℝ} (hu : 0 ≤ u) :
    (X.b ω u).Nonneg := by
  refine ⟨fun k => (hω.2.2.1 k u hu).1, fun i => ?_⟩
  show 0 ≤ ∑ j ∈ N.Ji i, X.Qij i j ω u / N.mu i j
  apply Finset.sum_nonneg
  intro j hj
  have hij : N.P i j = true := by simpa [Network.Ji] using hj
  exact div_nonneg (hω.2.2.2.1 i j u hij hu).1 (N.mu_pos i j hij).le

theorem bhat_eq (X : Run M r) (ω : Ω) (s : ℝ) :
    X.bhat ω s = ((r : ℝ) * ((r : ℝ) ^ 2)⁻¹) • X.toPaths.b ω ((r : ℝ) ^ 2 * s) := by
  ext k
  · simp only [Run.bhat, Run.Qhat, Paths.b, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [Run.bhat, Run.What, Paths.b, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring

theorem tau_mono (X : PolicyRun M r) {ω : Ω}
    (hpol : (∀ t : ℝ, 0 ≤ t →
      QPOpt N (X.toPaths.b ω t) ⟨fun j => X.ystar j ω t, fun i j => X.qstar i j ω t⟩) ∧
    (∀ i, X.tau i 1 ω = 0) ∧
    (∀ i n, 1 ≤ n → X.tau i n ω = ⊤ → X.tau i (n + 1) ω = ⊤) ∧
    (∀ i n, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → X.tau i n ω = ENNReal.ofReal t →
      (Jgt X.toPaths X.qstar i ω t = ∅ → Step2Rule M r X.toPaths i ω t (X.tau i (n + 1) ω)) ∧
      (Jgt X.toPaths X.qstar i ω t ≠ ∅ → Step3Rule M X.toPaths X.qstar i ω t (X.tau i (n + 1) ω))))
    (i : Fin N.I) (n : ℕ) (hn : 1 ≤ n) : X.tau i n ω ≤ X.tau i (n + 1) ω := by
  by_cases htop : X.tau i n ω = ⊤
  · rw [hpol.2.2.1 i n hn htop, htop]
  · set t := (X.tau i n ω).toReal
    have ht : X.tau i n ω = ENNReal.ofReal t := (ENNReal.ofReal_toReal htop).symm
    have h := hpol.2.2.2 i n hn t ENNReal.toReal_nonneg ht
    rw [ht]
    by_cases hJ : Jgt X.toPaths X.qstar i ω t = ∅
    · have h2 := (h.1 hJ).2.1
      by_cases htop' : X.tau i (n + 1) ω = ⊤
      · rw [htop']; exact le_top
      · have he := (ENNReal.ofReal_toReal htop').symm
        have := (h2 _ ENNReal.toReal_nonneg he).1
        rw [he]; exact ENNReal.ofReal_le_ofReal this.le
    · obtain ⟨m, _, _, _, _, heq⟩ := h.2 hJ
      rw [heq]
      exact le_iInf₂ (fun s hs => ENNReal.ofReal_le_ofReal hs.1)

end Run


section Cover

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Model N Ω P} {r : ℕ}

theorem cover (X : PolicyRun M r) {ω : Ω}
    (hpol : (∀ t : ℝ, 0 ≤ t →
      QPOpt N (X.toPaths.b ω t) ⟨fun j => X.ystar j ω t, fun i j => X.qstar i j ω t⟩) ∧
    (∀ i, X.tau i 1 ω = 0) ∧
    (∀ i n, 1 ≤ n → X.tau i n ω = ⊤ → X.tau i (n + 1) ω = ⊤) ∧
    (∀ i n, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → X.tau i n ω = ENNReal.ofReal t →
      (Jgt X.toPaths X.qstar i ω t = ∅ → Step2Rule M r X.toPaths i ω t (X.tau i (n + 1) ω)) ∧
      (Jgt X.toPaths X.qstar i ω t ≠ ∅ → Step3Rule M X.toPaths X.qstar i ω t (X.tau i (n + 1) ω))))
    (hadm : X.toPaths.IsAdmissibleAt M r ω)
    (T C5 C6 C7 ε₂ : ℝ) (hC7 : 0 ≤ C7) (hε₂ : 0 ≤ ε₂) (i : Fin N.I)
    (hMr : ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i (N.Mr T r) ω)
    (hA : ω ∈ ⋂ n ∈ Finset.Icc 1 (N.Mr T r), X.Aev T C5 C6 C7 ε₂ i n)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ (r : ℝ) ^ 2 * T) (j : Fin N.J) (hj : j ∈ N.Ji i) :
    |X.Qij i j ω t - X.qstar i j ω t| ≤ C5 * ε₂ * r + C7 * ε₂ * r + C6 * ε₂ * r := by
  classical
  have htT' : ENNReal.ofReal t ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) := ENNReal.ofReal_le_ofReal htT
  have hMr1 : 1 ≤ N.Mr T r := by unfold Network.Mr; omega
  set S := (Finset.Icc 1 (N.Mr T r)).filter (fun n => X.tau i n ω ≤ ENNReal.ofReal t)
  have h1S : 1 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hMr1⟩, by rw [hpol.2.1 i]; exact zero_le⟩
  set n := S.max' ⟨1, h1S⟩
  have hnS : n ∈ S := S.max'_mem _
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hnS
  obtain ⟨⟨hn1, hnM⟩, hnt⟩ := hnS
  have hnM' : n ≠ N.Mr T r := by
    intro h; rw [h] at hnt
    exact absurd (lt_of_le_of_lt (hnt.trans htT') hMr) (lt_irrefl _)
  have hnext : ENNReal.ofReal t < X.tau i (n + 1) ω := by
    by_contra hle; push Not at hle
    have hmem : n + 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, hle⟩
    have := S.le_max' _ hmem
    omega
  have hnI : n ∈ Finset.Icc 1 (N.Mr T r) := Finset.mem_Icc.2 ⟨hn1, hnM⟩
  have hAn := Set.mem_iInter₂.1 hA n hnI
  obtain ⟨⟨⟨_, hA2⟩, hA3⟩, _⟩ := hAn
  have hnT : ¬ (ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i n ω) := not_lt.2 (hnt.trans htT')
  have hntop : X.tau i n ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnt
  set τ := (X.tau i n ω).toReal
  have hτ : X.tau i n ω = ENNReal.ofReal τ := (ENNReal.ofReal_toReal hntop).symm
  have b2 : |X.Qij i j ω t - X.Qij i j ω τ| ≤ C5 * ε₂ * r := by
    rcases hA2 with h | h
    · exact absurd h hnT
    · exact h j hj t ht0 hnt hnext.le
  have b3 : |X.qstar i j ω t - X.qstar i j ω τ| ≤ C6 * ε₂ * r := by
    rcases hA3 with h | h
    · exact absurd h hnT
    · exact h j hj t ht0 hnt hnext.le
  have hij : N.P i j = true := by simpa [Network.Ji] using hj
  have b4 : |X.Qij i j ω τ - X.qstar i j ω τ| ≤ C7 * ε₂ * r := by
    rcases Nat.lt_or_ge 1 n with hlt | hle
    · -- previous period
      set m := n - 1
      have hm1 : 1 ≤ m := by omega
      have hmn : m + 1 = n := by omega
      have hmI : m ∈ Finset.Icc 1 (N.Mr T r) := Finset.mem_Icc.2 ⟨hm1, by omega⟩
      obtain ⟨_, hA4⟩ := Set.mem_iInter₂.1 hA m hmI
      have hmono := tau_mono X hpol i m hm1
      rw [hmn] at hmono
      have hmT : ¬ (ENNReal.ofReal ((r : ℝ) ^ 2 * T) < X.tau i m ω) :=
        not_lt.2 ((hmono.trans hnt).trans htT')
      rcases hA4 with h | h
      · exact absurd h hmT
      · rw [hmn] at h
        exact h j hj τ ENNReal.toReal_nonneg hτ
    · have hn : n = 1 := by omega
      have h0 : τ = 0 := by simp [τ, hn, hpol.2.1 i]
      rw [h0]
      have hQ0 : X.Qij i j ω 0 = 0 := (hadm.2.2.2.2.2.2.2.2.2.2.2.2.2 i j hij).1
      have hq0 : X.qstar i j ω 0 = 0 := by
        have hopt := (hpol.1 0 le_rfl).1.1
        have hsum := hopt.2.2.1 i
        have hW0 : (X.toPaths.b ω 0).2 i = 0 := by
          show ∑ j ∈ N.Ji i, X.Qij i j ω 0 / N.mu i j = 0
          apply Finset.sum_eq_zero
          intro j' hj'
          have hij' : N.P i j' = true := by simpa [Network.Ji] using hj'
          rw [(hadm.2.2.2.2.2.2.2.2.2.2.2.2.2 i j' hij').1, zero_div]
        rw [hW0] at hsum
        have hnn : ∀ j' ∈ N.Ji i, 0 ≤ X.qstar i j' ω 0 / N.mu i j' := by
          intro j' hj'
          have hij' : N.P i j' = true := by simpa [Network.Ji] using hj'
          exact div_nonneg (hopt.2.2.2.1 i j' hij') (N.mu_pos i j' hij').le
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum j hj
        rcases div_eq_zero_iff.1 this with h | h
        · exact h
        · exact absurd h (N.mu_pos i j hij).ne'
      rw [hQ0, hq0, sub_zero, abs_zero]
      positivity
  calc |X.Qij i j ω t - X.qstar i j ω t|
      = |(X.Qij i j ω t - X.Qij i j ω τ) + (X.Qij i j ω τ - X.qstar i j ω τ) +
          -(X.qstar i j ω t - X.qstar i j ω τ)| := by ring_nf
    _ ≤ |X.Qij i j ω t - X.Qij i j ω τ| + |X.Qij i j ω τ - X.qstar i j ω τ| +
          |-(X.qstar i j ω t - X.qstar i j ω τ)| := abs_add_three _ _ _
    _ ≤ C5 * ε₂ * r + C7 * ε₂ * r + C6 * ε₂ * r := by
        rw [abs_neg]; linarith

end Cover


theorem lamMin_pos (N : Network) : 0 < N.lamMin := by
  unfold Network.lamMin
  rw [Finset.lt_inf'_iff]
  intro j _; exact N.lam_pos j

theorem muMin_pos (N : Network) : 0 < N.muMin := by
  unfold Network.muMin
  rw [Finset.lt_inf'_iff]
  intro p hp
  have : N.P p.1 p.2 = true := by simpa [Network.pairs] using hp
  exact N.mu_pos _ _ this

theorem muMin_le_muBar (N : Network) : N.muMin ≤ N.muBar := by
  unfold Network.muMin Network.muBar
  obtain ⟨p, hp⟩ := N.pairs_nonempty
  exact (Finset.inf'_le (fun p => N.mu p.1 p.2) hp).trans (Finset.le_sup' (fun p => N.mu p.1 p.2) hp)

theorem lamMin_le_lamBar (N : Network) : N.lamMin ≤ N.lamBar := by
  unfold Network.lamMin Network.lamBar
  exact (Finset.inf'_le _ (Finset.mem_univ ⟨0, N.J_pos⟩)).trans
    (Finset.le_sup' _ (Finset.mem_univ _))

end FJP3

theorem solution {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (ε T : ℝ) (hε : 0 < ε) (hT : 0 < T) :
    Tendsto (fun r : ℕ => P {ω | ∃ s ∈ Set.Icc 0 T,
        ε < |∑ j, N.h j * (run r).Nhat j ω s - z N ((run r).bhat ω s)|})
      atTop (𝓝 0) := by
  -- constants of (37)
  have hlm := FJP3.lamMin_pos N
  have hmm := FJP3.muMin_pos N
  have hmb : 0 < N.muBar := lt_of_lt_of_le hmm (FJP3.muMin_le_muBar N)
  have hlb : 0 < N.lamBar := lt_of_lt_of_le hlm (FJP3.lamMin_le_lamBar N)
  set C5 : ℝ := 4 * N.lamBar + 2 * N.muBar + 1 with hC5
  set C7 : ℝ := N.lamMin / 4 with hC7
  set K : ℝ := 3 + 2 * ((N.J : ℝ) - 1) * (N.muBar / N.muMin) with hK
  have hJ1 : (1 : ℝ) ≤ N.J := by exact_mod_cast N.J_pos
  have hKpos : 3 ≤ K := by
    have : 0 ≤ 2 * ((N.J : ℝ) - 1) * (N.muBar / N.muMin) :=
      mul_nonneg (by linarith) (div_nonneg hmb.le hmm.le)
    linarith
  set C6 : ℝ := C7 / (2 * K) with hC6
  have hC5p : 0 < C5 := by positivity
  have hC7p : 0 < C7 := by positivity
  have hC6p : 0 < C6 := by positivity
  have h37a : max (4 * N.lamBar) (2 * N.muBar) < C5 := max_lt (by linarith) (by linarith)
  have h37b : K * C6 < C7 := by
    rw [hC6, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have h37c : C7 < 0.5 * N.lamMin := by rw [hC7]; linarith
  set H : ℝ := ∑ j, N.h j with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun j _ => N.h_nonneg j)
  set ε₂ : ℝ := ε / (2 * ((H + 1) * (((N.I : ℝ) + 1) * (C5 + C6 + C7)))) with hε₂
  have hε₂p : 0 < ε₂ := by positivity
  have hL4 : ∀ i, Tendsto (fun r : ℕ =>
      P (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ) atTop (𝓝 0) :=
    fun i => ForkJoinCtrl.Tracking.lemma_4_compl M hA1 hA2 run T hT C5 C6 C7 hC5p hC6p hC7p
      h37a h37b h37c ε₂ hε₂p i
  have h35 : ∀ i, Tendsto (fun r : ℕ =>
      P {ω | (run r).tau i (N.Mr T r) ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T)}) atTop (𝓝 0) :=
    fun i => ForkJoinCtrl.Tracking.eq_35 M hA1 hA2 run T hT i
  -- the bad set
  set Bad : ℕ → Set Ω := fun r => {ω | ¬ (run r).toPaths.IsAdmissibleAt M r ω} ∪
    {ω | ¬ ((∀ t : ℝ, 0 ≤ t → QPOpt N ((run r).toPaths.b ω t)
        ⟨fun j => (run r).ystar j ω t, fun i j => (run r).qstar i j ω t⟩) ∧
      (∀ i, (run r).tau i 1 ω = 0) ∧
      (∀ i n, 1 ≤ n → (run r).tau i n ω = ⊤ → (run r).tau i (n + 1) ω = ⊤) ∧
      (∀ i n, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → (run r).tau i n ω = ENNReal.ofReal t →
        (Jgt (run r).toPaths (run r).qstar i ω t = ∅ →
          Step2Rule M r (run r).toPaths i ω t ((run r).tau i (n + 1) ω)) ∧
        (Jgt (run r).toPaths (run r).qstar i ω t ≠ ∅ →
          Step3Rule M (run r).toPaths (run r).qstar i ω t ((run r).tau i (n + 1) ω))))}
  have hBad : ∀ r, P (Bad r) = 0 := fun r =>
    measure_union_null (ae_iff.1 (run r).adm) (ae_iff.1 (run r).policy)
  set G : ℕ → ENNReal := fun r => P (Bad r) +
    (∑ i, P {ω | (run r).tau i (N.Mr T r) ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T)} +
     ∑ i, P (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ)
  have hG : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun r => P (Bad r)) atTop (𝓝 0) := by simp [hBad]
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin N.I)) (fun i _ => h35 i)
    have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin N.I)) (fun i _ => hL4 i)
    simp only [Finset.sum_const_zero] at h2 h3
    have := h1.add (h2.add h3)
    simp only [add_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_ge_atTop 1] with r hr1
  set E := {ω | ∃ s ∈ Set.Icc 0 T,
        ε < |∑ j, N.h j * (run r).Nhat j ω s - z N ((run r).bhat ω s)|}
  have hsub : E ⊆ Bad r ∪ ((⋃ i, {ω | (run r).tau i (N.Mr T r) ω ≤
      ENNReal.ofReal ((r : ℝ) ^ 2 * T)}) ∪
      ⋃ i, (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ) := by
    intro ω hω
    by_contra hnot
    simp only [Bad, Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq,
      not_or, not_not, not_exists, not_le] at hnot
    obtain ⟨⟨hadm, hpol⟩, hτ, hAev⟩ := hnot
    obtain ⟨s, hs, hlt⟩ := hω
    have hr : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    set u := (r : ℝ) ^ 2 * s
    have hu0 : 0 ≤ u := by have := hs.1; positivity
    have huT : u ≤ (r : ℝ) ^ 2 * T := mul_le_mul_of_nonneg_left hs.2 (by positivity)
    set c : ℝ := (r : ℝ) * ((r : ℝ) ^ 2)⁻¹
    have hc : 0 < c := by positivity
    have hcr : c * r = 1 := by
      simp only [c]; field_simp
    have hopt := hpol.1 u hu0
    have hbn := FJP3.b_nonneg (run r).toPaths hadm hu0
    have hz : z N ((run r).bhat ω s) = c * ∑ j, N.h j * N.jobMax j (fun k => (run r).Qk k ω u)
        (fun i => (run r).qstar i j ω u) := by
      rw [FJP3.bhat_eq, FJP3.z_smul hc, FJP3.z_eq_obj17 _ hbn _ hopt]
      rfl
    have hN : ∀ j, (run r).Nhat j ω s = c * N.jobMax j (fun k => (run r).Qk k ω u)
        (fun i => (run r).Qij i j ω u) := by
      intro j
      rw [← FJP3.Nj_eq (run r).toPaths hadm j hu0]
      simp only [Run.Nhat, c, u]; ring
    have hdiff : ∑ j, N.h j * (run r).Nhat j ω s - z N ((run r).bhat ω s) =
        c * ∑ j, N.h j * (N.jobMax j (fun k => (run r).Qk k ω u) (fun i => (run r).Qij i j ω u) -
          N.jobMax j (fun k => (run r).Qk k ω u) (fun i => (run r).qstar i j ω u)) := by
      rw [hz]; simp only [hN, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
    set B := C5 * ε₂ * r + C7 * ε₂ * r + C6 * ε₂ * r
    have hcov : ∀ j, ∀ i ∈ N.Ij j, |(run r).Qij i j ω u - (run r).qstar i j ω u| ≤ B := by
      intro j i hi
      have hij : N.P i j = true := by simpa [Network.Ij] using hi
      have hj : j ∈ N.Ji i := by simp [Network.Ji, hij]
      exact FJP3.cover (run r) hpol hadm T C5 C6 C7 ε₂ hC7p.le hε₂p.le i (hτ i) (hAev i) u hu0
        huT j hj
    have hB0 : 0 ≤ B := by positivity
    have hbound : |∑ j, N.h j * (N.jobMax j (fun k => (run r).Qk k ω u)
        (fun i => (run r).Qij i j ω u) -
          N.jobMax j (fun k => (run r).Qk k ω u) (fun i => (run r).qstar i j ω u))| ≤
        H * ((N.I : ℝ) * B) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hH, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (N.h_nonneg j)]
      apply mul_le_mul_of_nonneg_left _ (N.h_nonneg j)
      refine (FJP3.jobMax_sub_le j _ _ _).trans ?_
      calc ∑ i ∈ N.Ij j, |(run r).Qij i j ω u - (run r).qstar i j ω u| ≤ ∑ i ∈ N.Ij j, B :=
            Finset.sum_le_sum (hcov j)
        _ = ((N.Ij j).card : ℝ) * B := by simp
        _ ≤ (N.I : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB0
            have := Finset.card_le_univ (N.Ij j)
            simp only [Fintype.card_fin] at this
            exact_mod_cast this
    rw [hdiff, abs_mul, abs_of_pos hc] at hlt
    have hfin : c * (H * ((N.I : ℝ) * B)) ≤ ε / 2 := by
      have hB : B = (C5 + C6 + C7) * ε₂ * r := by simp only [B]; ring
      rw [hB]
      have e : c * (H * ((N.I : ℝ) * ((C5 + C6 + C7) * ε₂ * r))) =
          (c * r) * (H * ((N.I : ℝ) * (C5 + C6 + C7))) * ε₂ := by ring
      rw [e, hcr, one_mul, hε₂]
      have hI0 : (0 : ℝ) ≤ N.I := Nat.cast_nonneg _
      have hC : 0 < C5 + C6 + C7 := by positivity
      set Y : ℝ := (H + 1) * (((N.I : ℝ) + 1) * (C5 + C6 + C7))
      have hY : 0 < Y := by positivity
      have hXY : H * ((N.I : ℝ) * (C5 + C6 + C7)) ≤ Y := by
        apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
        exact mul_le_mul_of_nonneg_right (by linarith) hC.le
      calc H * ((N.I : ℝ) * (C5 + C6 + C7)) * (ε / (2 * Y)) ≤ Y * (ε / (2 * Y)) :=
            mul_le_mul_of_nonneg_right hXY (by positivity)
        _ = ε / 2 := by field_simp
    have := mul_le_mul_of_nonneg_left hbound hc.le
    linarith
  calc P E ≤ P (Bad r ∪ ((⋃ i, {ω | (run r).tau i (N.Mr T r) ω ≤
      ENNReal.ofReal ((r : ℝ) ^ 2 * T)}) ∪
      ⋃ i, (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ)) := measure_mono hsub
    _ ≤ P (Bad r) + (P (⋃ i, {ω | (run r).tau i (N.Mr T r) ω ≤
      ENNReal.ofReal ((r : ℝ) ^ 2 * T)}) +
      P (⋃ i, (⋂ n ∈ Finset.Icc 1 (N.Mr T r), (run r).Aev T C5 C6 C7 ε₂ i n)ᶜ)) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ G r := by
        apply add_le_add le_rfl
        exact add_le_add (measure_iUnion_fintype_le _ _) (measure_iUnion_fintype_le _ _)
