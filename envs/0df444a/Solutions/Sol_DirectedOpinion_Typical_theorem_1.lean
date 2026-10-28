-- Prove2me | solution 1 for DirectedOpinion.Typical.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:35:20.619982+00:00
-- url     : https://prove2.me/submissions/736f56b3-7db3-41d4-bdec-aa67f83617d8

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_Model

namespace DirectedOpinion.Typical.T1Aux

open MeasureTheory ProbabilityTheory Set Filter Topology DirectedOpinion.Typical

variable {V : Type*} (G : WDigraph V) (c d : ℝ)

/-- `Δ` as a linear map. -/
def ΔL : Module.End ℝ (V → ℝ) where
  toFun := Δ G c d
  map_add' f g := by
    funext i; simp only [Δ, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
  map_smul' a f := by
    funext i; simp only [Δ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun r _ => by ring
    · ring

lemma ΔL_apply (f : V → ℝ) : ΔL G c d f = Δ G c d f := rfl

lemma iter_eq (n : ℕ) (f : V → ℝ) : (Δ G c d)^[n] f = (ΔL G c d ^ n) f := by
  rw [Module.End.coe_pow]; rfl

variable {G c d}

lemma Δ_nonneg (hcd : c + d ≤ 1) (hG : G.Valid c) {f : V → ℝ} (hf : ∀ v, 0 ≤ f v) (i : V) :
    0 ≤ Δ G c d f i := by
  unfold Δ
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg (hG.1 i r (Finset.mem_range.1 hr)).1 (hf _)
  · exact mul_nonneg (by linarith) (hf i)

lemma pow_nonneg' (hcd : c + d ≤ 1) (hG : G.Valid c) (n : ℕ) {f : V → ℝ} (hf : ∀ v, 0 ≤ f v)
    (i : V) : 0 ≤ (ΔL G c d ^ n) f i := by
  induction n generalizing i with
  | zero => simpa using hf i
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ΔL_apply]
    exact Δ_nonneg hcd hG ih i

lemma pow_mono (hcd : c + d ≤ 1) (hG : G.Valid c) (n : ℕ) {f g : V → ℝ} (h : ∀ v, f v ≤ g v)
    (i : V) : (ΔL G c d ^ n) f i ≤ (ΔL G c d ^ n) g i := by
  have := pow_nonneg' hcd hG n (f := g - f) (fun v => by simp [h v]) i
  rw [map_sub] at this
  simpa [sub_nonneg] using this

lemma pow_abs_le (hcd : c + d ≤ 1) (hG : G.Valid c) (n : ℕ) (f : V → ℝ) (i : V) :
    |(ΔL G c d ^ n) f i| ≤ (ΔL G c d ^ n) (fun v => |f v|) i := by
  rw [abs_le]
  constructor
  · have := pow_mono hcd hG n (f := fun v => -|f v|) (g := f) (fun v => neg_abs_le _) i
    have e : (fun v => -|f v|) = -(fun v => |f v|) := rfl
    rw [e, map_neg] at this
    simpa using this
  · exact pow_mono hcd hG n (fun v => le_abs_self _) i

lemma Δ_norm (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) {f : V → ℝ} {M : ℝ}
    (hf : ∀ v, |f v| ≤ M) (i : V) : |Δ G c d f i| ≤ (1 - d) * M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf i)
  unfold Δ
  have h1 : |∑ r ∈ Finset.range (G.deg i), G.wt i r * f (G.nbr i r)| ≤
      ∑ r ∈ Finset.range (G.deg i), G.wt i r * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hw := hG.1 i r (Finset.mem_range.1 hr)
    rw [abs_mul, abs_of_nonneg hw.1]
    exact mul_le_mul_of_nonneg_left (hf _) hw.1
  have h2 : |(1 - c - d) * f i| ≤ (1 - c - d) * M := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left (hf _) (by linarith)
  rw [← Finset.sum_mul] at h1
  have hs : ∑ r ∈ Finset.range (G.deg i), G.wt i r ≤ c := by
    rcases Nat.eq_zero_or_pos (G.deg i) with h | h
    · simp [h, hc0]
    · exact (hG.2 i h).le
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (∑ r ∈ Finset.range (G.deg i), G.wt i r) * M + (1 - c - d) * M := add_le_add h1 h2
    _ ≤ c * M + (1 - c - d) * M := by gcongr
    _ = (1 - d) * M := by ring

lemma pow_norm (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) (n : ℕ) {f : V → ℝ} {M : ℝ}
    (hf : ∀ v, |f v| ≤ M) (i : V) : |(ΔL G c d ^ n) f i| ≤ (1 - d) ^ n * M := by
  induction n generalizing i with
  | zero => simpa using hf i
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ΔL_apply]
    have := Δ_norm hc0 hcd hG ih i
    rw [pow_succ]; linarith

lemma budget_eq (hc0 : 0 ≤ c) (hG : G.Valid c) (i : V) :
    0 ≤ G.budget c d i - d ∧ G.budget c d i ≤ c + d := by
  unfold WDigraph.budget
  have hs : 0 ≤ ∑ r ∈ Finset.range (G.deg i), G.wt i r :=
    Finset.sum_nonneg fun r hr => (hG.1 i r (Finset.mem_range.1 hr)).1
  have hs' : ∑ r ∈ Finset.range (G.deg i), G.wt i r ≤ c := by
    rcases Nat.eq_zero_or_pos (G.deg i) with h | h
    · simp [h, hc0]
    · exact (hG.2 i h).le
  constructor <;> linarith

lemma Δ_one (i : V) : Δ G c d (fun _ => 1) i = 1 - G.budget c d i := by
  simp [Δ, WDigraph.budget]; ring

lemma telescope (n : ℕ) :
    ∑ s ∈ Finset.range n, (ΔL G c d ^ s) (G.budget c d) =
      (fun _ => (1 : ℝ)) - (ΔL G c d ^ n) (fun _ => 1) := by
  have hb : G.budget c d = (fun _ => (1 : ℝ)) - ΔL G c d (fun _ => 1) := by
    funext i; simp [ΔL_apply, Δ_one]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hb, map_sub, pow_succ, Module.End.mul_apply]
    abel

/-- The key bound: a sum `Σ_{s<n} Δ^s w_s` with `|w_s| ≤ budget` is bounded by `1 - Δ^n 1`. -/
lemma partial_bound (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) (w : ℕ → V → ℝ)
    (hw : ∀ s j, |w s j| ≤ G.budget c d j) (n : ℕ) (i : V) :
    |(∑ s ∈ Finset.range n, (ΔL G c d ^ s) (w s)) i| ≤ 1 - (ΔL G c d ^ n) (fun _ => 1) i := by
  have key : (∑ s ∈ Finset.range n, (ΔL G c d ^ s) (G.budget c d)) i =
      1 - (ΔL G c d ^ n) (fun _ => 1) i := by
    rw [telescope]; rfl
  rw [← key, Finset.sum_apply, Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  exact (pow_abs_le hcd hG s _ i).trans (pow_mono hcd hG s (hw s) i)

lemma partial_bound_one (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) (w : ℕ → V → ℝ)
    (hw : ∀ s j, |w s j| ≤ G.budget c d j) (n : ℕ) (i : V) :
    |(∑ s ∈ Finset.range n, (ΔL G c d ^ s) (w s)) i| ≤ 1 := by
  have := partial_bound hc0 hcd hG w hw n i
  have := pow_nonneg' hcd hG n (f := fun _ => (1 : ℝ)) (fun _ => zero_le_one) i
  linarith

lemma opinion_eq (R0 : V → ℝ) (W : ℕ → V → ℝ) (k : ℕ) :
    opinion G c d R0 W k =
      (ΔL G c d ^ k) R0 + ∑ s ∈ Finset.range k, (ΔL G c d ^ s) (W (k - 1 - s)) := by
  induction k with
  | zero => simp [opinion]
  | succ k ih =>
    have e : opinion G c d R0 W (k + 1) = ΔL G c d (opinion G c d R0 W k) + W k := by
      funext i; simp [opinion, ΔL_apply]
    rw [e, ih, map_add, map_sum, Finset.sum_range_succ']
    have h1 : ∀ s ∈ Finset.range k, (ΔL G c d ^ (s + 1)) (W (k + 1 - 1 - (s + 1))) =
        ΔL G c d ((ΔL G c d ^ s) (W (k - 1 - s))) := by
      intro s _
      rw [pow_succ', Module.End.mul_apply, show k + 1 - 1 - (s + 1) = k - 1 - s by omega]
    rw [Finset.sum_congr rfl h1, pow_succ', Module.End.mul_apply]
    simp only [pow_zero, Module.End.one_apply, Nat.add_sub_cancel, Nat.sub_zero]
    abel

lemma opinion_bound (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) (R0 : V → ℝ)
    (hR0 : ∀ v, R0 v ∈ Icc (-1 : ℝ) 1) (W : ℕ → V → ℝ)
    (hW : ∀ s j, |W s j| ≤ G.budget c d j) (k : ℕ) (i : V) :
    |opinion G c d R0 W k i| ≤ 1 := by
  rw [opinion_eq, Pi.add_apply]
  have h1 := partial_bound hc0 hcd hG (fun s => W (k - 1 - s)) (fun s j => hW _ j) k i
  have h2 : |(ΔL G c d ^ k) R0 i| ≤ (ΔL G c d ^ k) (fun _ => 1) i :=
    (pow_abs_le hcd hG k R0 i).trans
      (pow_mono hcd hG k (fun v => abs_le.2 ⟨(hR0 v).1, (hR0 v).2⟩) i)
  linarith [abs_add_le ((ΔL G c d ^ k) R0 i)
    ((∑ s ∈ Finset.range k, (ΔL G c d ^ s) (W (k - 1 - s))) i)]

lemma term_bound (hc0 : 0 ≤ c) (hcd : c + d ≤ 1) (hG : G.Valid c) (w : ℕ → V → ℝ)
    (hw : ∀ s j, |w s j| ≤ G.budget c d j) (s : ℕ) (i : V) :
    ‖(ΔL G c d ^ s) (w s) i‖ ≤ (c + d) * (1 - d) ^ s := by
  rw [Real.norm_eq_abs, mul_comm]
  exact pow_norm hc0 hcd hG s (fun j => (hw s j).trans (budget_eq hc0 hG j).2) i

lemma summable_terms (hc0 : 0 ≤ c) (hd0 : 0 < d) (hcd : c + d ≤ 1) (hG : G.Valid c)
    (w : ℕ → V → ℝ) (hw : ∀ s j, |w s j| ≤ G.budget c d j) (i : V) :
    Summable (fun s => (ΔL G c d ^ s) (w s) i) :=
  Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left (c + d))
    (term_bound hc0 hcd hG w hw · i)

lemma tsum_bound (hc0 : 0 ≤ c) (hd0 : 0 < d) (hcd : c + d ≤ 1) (hG : G.Valid c)
    (w : ℕ → V → ℝ) (hw : ∀ s j, |w s j| ≤ G.budget c d j) (i : V) :
    |∑' s, (ΔL G c d ^ s) (w s) i| ≤ 1 := by
  have t := (summable_terms hc0 hd0 hcd hG w hw i).hasSum.tendsto_sum_nat
  refine le_of_tendsto' t.abs fun n => ?_
  have := partial_bound_one hc0 hcd hG w hw n i
  rwa [Finset.sum_apply] at this

lemma tail_bound (hc0 : 0 ≤ c) (hd0 : 0 < d) (hcd : c + d ≤ 1) (hG : G.Valid c)
    (w : ℕ → V → ℝ) (hw : ∀ s j, |w s j| ≤ G.budget c d j) (k : ℕ) (i : V) :
    |(∑ s ∈ Finset.range k, (ΔL G c d ^ s) (w s)) i - ∑' s, (ΔL G c d ^ s) (w s) i| ≤
      (1 - d) ^ k * ((c + d) / d) := by
  rw [← (summable_terms hc0 hd0 hcd hG w hw i).sum_add_tsum_nat_add k, Finset.sum_apply]
  rw [sub_add_cancel_left, abs_neg]
  have hg : HasSum (fun s : ℕ => (c + d) * (1 - d) ^ k * (1 - d) ^ s)
      ((c + d) * (1 - d) ^ k * (1 - (1 - d))⁻¹) :=
    (hasSum_geometric_of_lt_one (by linarith) (by linarith)).mul_left _
  have := tsum_of_norm_bounded (f := fun s => (ΔL G c d ^ (s + k)) (w (s + k)) i) hg
    (fun s => (term_bound hc0 hcd hG w hw (s + k) i).trans (le_of_eq (by rw [pow_add]; ring)))
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [sub_sub_cancel, div_eq_mul_inv]
  ring

/-- Uniform continuity of a continuous function on the cube `[-1,1]^V` for the sup distance. -/
lemma unif_cube {W : Type*} (g : (W → ℝ) → ℝ) (hg : Continuous g) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : W → ℝ, (∀ j, |x j| ≤ 1) → (∀ j, |y j| ≤ 1) →
      (∀ j, |x j - y j| < δ) → |g x - g y| < ε := by
  set K : Set (W → ℝ) := Set.pi univ (fun _ => Icc (-1 : ℝ) 1)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hU := hK.uniformContinuousOn_of_continuous hg.continuousOn
  have h1 : {p : ℝ × ℝ | dist p.1 p.2 < ε} ∈ uniformity ℝ := Metric.dist_mem_uniformity hε
  have h2 := hU h1
  rw [Filter.mem_map, Filter.mem_inf_principal] at h2
  have h3 := UniformFun.uniformContinuous_toFun (α := W) (β := ℝ) h2
  rw [Filter.mem_map] at h3
  obtain ⟨δ, hδ, hsub⟩ :=
    (UniformFun.hasBasis_uniformity_of_basis W ℝ Metric.uniformity_basis_dist).mem_iff.1 h3
  refine ⟨δ, hδ, fun x y hx hy hxy => ?_⟩
  have hmem : (UniformFun.ofFun x, UniformFun.ofFun y) ∈
      UniformFun.gen W ℝ {p : ℝ × ℝ | dist p.1 p.2 < δ} := by
    intro j
    simpa [Real.dist_eq] using hxy j
  have := hsub hmem
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
  have hxK : x ∈ K := fun j _ => abs_le.1 (hx j)
  have hyK : y ∈ K := fun j _ => abs_le.1 (hy j)
  have := this ⟨hxK, hyK⟩
  simpa [Real.dist_eq] using this

end DirectedOpinion.Typical.T1Aux

open MeasureTheory ProbabilityTheory Set Filter Topology DirectedOpinion.Typical
  DirectedOpinion.Typical.T1Aux

theorem solution {V Ω : Type*} [Countable V] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : WDigraph V) (c d : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1) (hG : G.Valid c) (hlf : G.LocallyFinite)
    (W : ℕ → V → Ω → ℝ) (hWm : ∀ k i, Measurable (W k i))
    (hWind : iIndepFun (fun p : ℕ × V => W p.1 p.2) P)
    (hWid : ∀ k i, IdentDistrib (W k i) (W 0 i) P P)
    (hWb : ∀ k i ω, |W k i ω| ≤ G.budget c d i) :
    (∀ ω i, stationary G c d (fun k j => W k j ω) i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ R0 : Ω → V → ℝ, Measurable R0 → (∀ ω i, R0 ω i ∈ Icc (-1 : ℝ) 1) →
      TendstoInDistribution (fun k ω => opinion G c d (R0 ω) (fun t j => W t j ω) k) atTop
          (fun ω => stationary G c d (fun t j => W t j ω)) (fun _ => P) P ∧
        ∀ (F : Finset V) (f : (F → ℝ) → ℝ), LipschitzWith 1 f → ∀ k : ℕ,
          |(∫ ω, f (fun j => opinion G c d (R0 ω) (fun t i => W t i ω) k j) ∂P) -
              ∫ ω, f (fun j => stationary G c d (fun t i => W t i ω) j) ∂P| ≤
            (1 - d) ^ k * (2 / d + 2) := by
  set L := ΔL G c d with hL
  have hWb' : ∀ ω, ∀ s j, |(fun t j => W t j ω) s j| ≤ G.budget c d j :=
    fun ω s j => hWb s j ω
  have hstat : ∀ ω, stationary G c d (fun k j => W k j ω) =
      fun i => ∑' s, (L ^ s) (fun j => W s j ω) i := by
    intro ω; funext i; simp only [stationary, iter_eq, hL]
  refine ⟨fun ω i => ?_, fun R0 hR0m hR0 => ?_⟩
  · rw [hstat]
    exact Set.mem_Icc.2 (abs_le.1 (tsum_bound hc0 hd0 hcd hG _ (hWb' ω) i))
  -- continuity and measurability
  have hLc : Continuous (L : (V → ℝ) → (V → ℝ)) := by
    refine continuous_pi fun i => ?_
    show Continuous fun f => Δ G c d f i
    unfold Δ
    fun_prop
  have hLnc : ∀ n, Continuous ((L ^ n : Module.End ℝ (V → ℝ)) : (V → ℝ) → (V → ℝ)) := by
    intro n; rw [Module.End.coe_pow]; exact hLc.iterate n
  have hWv : ∀ s, Measurable (fun ω => fun j => W s j ω) :=
    fun s => measurable_pi_lambda _ (hWm s)
  let B : ℕ → Ω → V → ℝ := fun n ω => ∑ s ∈ Finset.range n, (L ^ s) (fun j => W s j ω)
  let A : ℕ → Ω → V → ℝ := fun n ω => ∑ s ∈ Finset.range n, (L ^ s) (fun j => W (n - 1 - s) j ω)
  let Rst : Ω → V → ℝ := fun ω i => ∑' s, (L ^ s) (fun j => W s j ω) i
  let X : ℕ → Ω → V → ℝ := fun k ω => opinion G c d (R0 ω) (fun t j => W t j ω) k
  have hX : ∀ k ω, X k ω = (L ^ k) (R0 ω) + A k ω := fun k ω => opinion_eq _ _ _
  have hBm : ∀ n, Measurable (B n) := fun n =>
    Finset.measurable_sum _ fun s _ => (hLnc s).measurable.comp (hWv s)
  have hAm : ∀ n, Measurable (A n) := fun n =>
    Finset.measurable_sum _ fun s _ => (hLnc s).measurable.comp (hWv _)
  have hXm : ∀ k, Measurable (X k) := by
    intro k
    have : X k = fun ω => (L ^ k) (R0 ω) + A k ω := funext (hX k)
    rw [this]
    exact ((hLnc k).measurable.comp hR0m).add (hAm k)
  have hBlim : ∀ ω, Tendsto (fun n => B n ω) atTop (𝓝 (Rst ω)) := by
    intro ω
    refine tendsto_pi_nhds.2 fun i => ?_
    have := (summable_terms hc0 hd0 hcd hG _ (hWb' ω) i).hasSum.tendsto_sum_nat
    simpa [B, Rst, Finset.sum_apply] using this
  have hRm : Measurable Rst := by
    refine measurable_pi_lambda _ fun i => ?_
    refine measurable_of_tendsto_metrizable (f := fun n ω => B n ω i)
      (fun n => (measurable_pi_apply i).comp (hBm n)) ?_
    exact tendsto_pi_nhds.2 fun ω => (continuous_apply i).continuousAt.tendsto.comp (hBlim ω)
  have hRst : (fun ω => stationary G c d (fun t j => W t j ω)) = Rst := funext hstat
  -- bounds
  have hXb : ∀ k ω j, |X k ω j| ≤ 1 := fun k ω j =>
    opinion_bound hc0 hcd hG (R0 ω) (hR0 ω) _ (hWb' ω) k j
  have hAb : ∀ k ω j, |A k ω j| ≤ 1 := fun k ω j =>
    partial_bound_one hc0 hcd hG (fun s j => W (k - 1 - s) j ω) (fun s j => hWb _ _ _) k j
  have hBb : ∀ k ω j, |B k ω j| ≤ 1 := fun k ω j =>
    partial_bound_one hc0 hcd hG _ (hWb' ω) k j
  have hRb : ∀ ω j, |Rst ω j| ≤ 1 := fun ω j => tsum_bound hc0 hd0 hcd hG _ (hWb' ω) j
  have hXA : ∀ k ω j, |X k ω j - A k ω j| ≤ (1 - d) ^ k := by
    intro k ω j
    rw [hX, Pi.add_apply, add_sub_cancel_right]
    have := pow_norm hc0 hcd hG k (f := R0 ω) (M := 1)
      (fun v => abs_le.2 ⟨(hR0 ω v).1, (hR0 ω v).2⟩) j
    simpa using this
  have hBR : ∀ k ω j, |B k ω j - Rst ω j| ≤ (1 - d) ^ k * ((c + d) / d) := by
    intro k ω j
    exact tail_bound hc0 hd0 hcd hG _ (hWb' ω) k j
  -- equality of laws
  have hlaw : ∀ n, P.map (A n) = P.map (B n) := by
    intro n
    let ψ : (Fin n × V → ℝ) → (V → ℝ) := fun x => ∑ s : Fin n, (L ^ (s : ℕ)) (fun j => x (s, j))
    have hψ : Measurable ψ := by
      refine Continuous.measurable (continuous_finsetSum _ fun s _ => ?_)
      exact (hLnc s).comp (continuous_pi fun j => continuous_apply ((s, j) : Fin n × V))
    let Xf : Ω → (Fin n × V → ℝ) := fun ω p => W p.1 p.2 ω
    let Xr : Ω → (Fin n × V → ℝ) := fun ω p => W (n - 1 - p.1) p.2 ω
    have hA : A n = ψ ∘ Xr := by
      funext ω
      simp only [A, ψ, Xr, Function.comp_apply]
      rw [Finset.sum_range (fun s => (L ^ s) (fun j => W (n - 1 - s) j ω))]
    have hB : B n = ψ ∘ Xf := by
      funext ω
      simp only [B, ψ, Xf, Function.comp_apply]
      rw [Finset.sum_range (fun s => (L ^ s) (fun j => W s j ω))]
    have hXf : Measurable Xf := measurable_pi_lambda _ fun p => hWm _ _
    have hXr : Measurable Xr := measurable_pi_lambda _ fun p => hWm _ _
    have hgf : Function.Injective (fun p : Fin n × V => ((p.1 : ℕ), p.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Fin.ext h.1) h.2
    have hgr : Function.Injective (fun p : Fin n × V => (n - 1 - (p.1 : ℕ), p.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      refine Prod.ext (Fin.ext ?_) h.2
      have := a.1.2; have := b.1.2; omega
    have e1 : P.map Xf = Measure.infinitePi (fun p : Fin n × V => P.map (W p.1 p.2)) :=
      (hWind.precomp hgf).map_fun_eq_infinitePi_map (fun p => hWm _ _)
    have e2 : P.map Xr = Measure.infinitePi (fun p : Fin n × V => P.map (W (n - 1 - p.1) p.2)) :=
      (hWind.precomp hgr).map_fun_eq_infinitePi_map (fun p => hWm _ _)
    have hmarg : (fun p : Fin n × V => P.map (W (n - 1 - p.1) p.2)) =
        fun p => P.map (W p.1 p.2) := by
      funext p; exact (hWid _ _).map_eq.trans (hWid _ _).map_eq.symm
    rw [hA, hB, ← Measure.map_map hψ hXr, ← Measure.map_map hψ hXf, e1, e2, hmarg]
  have hint : ∀ n (h : (V → ℝ) → ℝ), Continuous h →
      ∫ ω, h (A n ω) ∂P = ∫ ω, h (B n ω) ∂P := by
    intro n h hh
    rw [← integral_map (hAm n).aemeasurable hh.aestronglyMeasurable, hlaw n,
      integral_map (hBm n).aemeasurable hh.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · -- convergence in distribution
    refine ⟨fun k => (hXm k).aemeasurable, by rw [hRst]; exact hRm.aemeasurable, ?_⟩
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g => ?_
    have key : Tendsto (fun n => ∫ ω, g (X n ω) ∂P) atTop (𝓝 (∫ ω, g (Rst ω) ∂P)) := by
      have hconvB : Tendsto (fun n => ∫ ω, g (B n ω) ∂P) atTop (𝓝 (∫ ω, g (Rst ω) ∂P)) := by
        refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
          (fun n => (g.continuous.measurable.comp (hBm n)).aestronglyMeasurable)
          (integrable_const _) (fun n => ae_of_all _ fun ω => g.norm_coe_le_norm _)
          (ae_of_all _ fun ω => (g.continuous.tendsto _).comp (hBlim ω))
      have hdiff : Tendsto (fun n => ∫ ω, g (X n ω) ∂P - ∫ ω, g (A n ω) ∂P) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨δ, hδ, hu⟩ := unif_cube (W := V) g g.continuous (ε / 2) (by linarith)
        obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by linarith : 1 - d < 1)
        refine ⟨N, fun n hn => ?_⟩
        have hpow : (1 - d) ^ n < δ :=
          lt_of_le_of_lt (pow_le_pow_of_le_one (by linarith) (by linarith) hn) hN
        have hi : ∀ (Y : Ω → V → ℝ), Measurable Y → Integrable (fun ω => g (Y ω)) P :=
          fun Y hY => Integrable.of_bound (g.continuous.measurable.comp hY).aestronglyMeasurable
            ‖g‖ (ae_of_all _ fun ω => g.norm_coe_le_norm _)
        rw [Real.dist_eq, sub_zero, ← integral_sub (hi _ (hXm n)) (hi _ (hAm n))]
        have := norm_integral_le_of_norm_le_const (μ := P)
          (f := fun ω => g (X n ω) - g (A n ω)) (C := ε / 2)
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs]
            exact (hu _ _ (hXb n ω) (hAb n ω) fun j => (hXA n ω j).trans_lt hpow).le)
        rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
        linarith
      have := hdiff.add hconvB
      rw [zero_add] at this
      refine this.congr fun n => ?_
      rw [hint n g g.continuous]; ring
    convert key using 2 with n
    · exact integral_map (hXm n).aemeasurable g.continuous.aestronglyMeasurable
    · show ∫ x, g x ∂(P.map (fun ω => stationary G c d fun t j => W t j ω)) = _
      rw [integral_map (by rw [hRst]; exact hRm.aemeasurable) g.continuous.aestronglyMeasurable]
      simp only [hstat]; rfl
  · intro F f hf k
    let h : (V → ℝ) → ℝ := fun y => f (fun j : F => y j)
    have hhc : Continuous h :=
      hf.continuous.comp (continuous_pi fun j => continuous_apply _)
    have hlip : ∀ x y : V → ℝ, ∀ r : ℝ, 0 ≤ r → (∀ j, |x j - y j| ≤ r) → |h x - h y| ≤ r := by
      intro x y r hr hxy
      have := hf.dist_le_mul (fun j : F => x j) (fun j : F => y j)
      rw [NNReal.coe_one, one_mul, Real.dist_eq] at this
      refine this.trans ((dist_pi_le_iff hr).2 fun j => ?_)
      rw [Real.dist_eq]; exact hxy j
    have hbd : ∀ x : V → ℝ, (∀ j, |x j| ≤ 1) → |h x| ≤ |h 0| + 1 := by
      intro x hx
      have := hlip x 0 1 zero_le_one (fun j => by simpa using hx j)
      have := abs_sub_abs_le_abs_sub (h x) (h 0)
      linarith
    have hi : ∀ (Y : Ω → V → ℝ), Measurable Y → (∀ ω j, |Y ω j| ≤ 1) →
        Integrable (fun ω => h (Y ω)) P :=
      fun Y hY hYb => Integrable.of_bound (hhc.measurable.comp hY).aestronglyMeasurable
        (|h 0| + 1) (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbd _ (hYb ω))
    show |∫ ω, h (X k ω) ∂P - ∫ ω, h (stationary G c d (fun t i => W t i ω)) ∂P| ≤ _
    simp only [hstat]
    show |∫ ω, h (X k ω) ∂P - ∫ ω, h (Rst ω) ∂P| ≤ _
    have e : ∫ ω, h (X k ω) ∂P - ∫ ω, h (Rst ω) ∂P =
        ∫ ω, (h (X k ω) - h (A k ω)) ∂P + ∫ ω, (h (B k ω) - h (Rst ω)) ∂P := by
      rw [integral_sub (hi _ (hXm k) (hXb k)) (hi _ (hAm k) (hAb k)),
        integral_sub (hi _ (hBm k) (hBb k)) (hi _ hRm hRb), hint k h hhc]
      ring
    have hk0 : 0 ≤ (1 - d) ^ k := pow_nonneg (by linarith) k
    have hcd0 : 0 ≤ (c + d) / d := div_nonneg (by linarith) hd0.le
    have b1 := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => h (X k ω) - h (A k ω)) (C := (1 - d) ^ k)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hlip _ _ _ hk0 (hXA k ω))
    have b2 := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => h (B k ω) - h (Rst ω)) (C := (1 - d) ^ k * ((c + d) / d))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact hlip _ _ _ (mul_nonneg hk0 hcd0) (hBR k ω))
    rw [Real.norm_eq_abs, probReal_univ, mul_one] at b1 b2
    rw [e]
    have h3 : (c + d) / d ≤ 2 / d + 1 := by
      have : (c + d) / d ≤ 2 / d := div_le_div_of_nonneg_right (by linarith) hd0.le
      linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ (1 - d) ^ k + (1 - d) ^ k * ((c + d) / d) := add_le_add b1 b2
      _ ≤ (1 - d) ^ k + (1 - d) ^ k * (2 / d + 1) := by gcongr
      _ = (1 - d) ^ k * (2 / d + 2) := by ring
