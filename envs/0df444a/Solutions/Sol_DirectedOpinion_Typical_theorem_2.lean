-- Prove2me | solution 1 for DirectedOpinion.Typical.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T04:51:13.307156+00:00
-- url     : https://prove2.me/submissions/dffab4a9-0963-402b-8796-59d5b3ba86fb

-- SPDX-License-Identifier: Apache-2.0
import Mathlib
import Definitions.Def_DirectedOpinion_Typical_GraphSeq

section
namespace DirectedOpinion.Typical.OpinionFresh
open Finset

 theorem weight_sum_nonneg {V : Type*} (G : WDigraph V) {c : ℝ}
    (hG : G.Valid c) (i : V) : 0 ≤ ∑ r ∈ range (G.deg i), G.wt i r :=
  sum_nonneg fun r hr => (hG.1 i r (mem_range.mp hr)).1

 theorem weight_sum_le {V : Type*} (G : WDigraph V) {c : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (i : V) : ∑ r ∈ range (G.deg i), G.wt i r ≤ c := by
  by_cases hi : 0 < G.deg i
  · exact (hG.2 i hi).le
  · have hz : G.deg i = 0 := by omega
    simpa [hz] using hc

 theorem budget_le_one {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hcd : c + d ≤ 1) (i : V) : G.budget c d i ≤ 1 := by
  have := weight_sum_nonneg G hG i
  unfold WDigraph.budget
  linarith

 theorem delta_abs_local {V : Type*} (G : WDigraph V) {c d M : ℝ}
    (hG : G.Valid c) (hcd : c + d ≤ 1) (f : V → ℝ)
    (hf : ∀ i, |f i| ≤ M) (i : V) :
    |Δ G c d f i| ≤ ((∑ r ∈ range (G.deg i), G.wt i r) + (1 - c - d)) * M := by
  have hp : 0 ≤ 1 - c - d := by linarith
  calc
    |Δ G c d f i| ≤ |∑ r ∈ range (G.deg i), G.wt i r * f (G.nbr i r)| +
        |(1 - c - d) * f i| := abs_add_le _ _
    _ ≤ (∑ r ∈ range (G.deg i), |G.wt i r * f (G.nbr i r)|) +
        |(1 - c - d) * f i| := add_le_add (abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ r ∈ range (G.deg i), G.wt i r * M) + (1 - c - d) * M := by
      apply add_le_add
      · apply sum_le_sum
        intro r hr
        rw [abs_mul, abs_of_nonneg (hG.1 i r (mem_range.mp hr)).1]
        exact mul_le_mul_of_nonneg_left (hf _) (hG.1 i r (mem_range.mp hr)).1
      · rw [abs_mul, abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (hf i) hp
    _ = _ := by rw [add_mul, sum_mul]

 theorem delta_abs_le {V : Type*} (G : WDigraph V) {c d M : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (hM : 0 ≤ M)
    (f : V → ℝ) (hf : ∀ i, |f i| ≤ M) (i : V) : |Δ G c d f i| ≤ (1 - d) * M := by
  apply (delta_abs_local G hG hcd f hf i).trans
  apply mul_le_mul_of_nonneg_right _ hM
  have := weight_sum_le G hG hc i
  linarith

 theorem opinion_abs_le_one {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hcd : c + d ≤ 1) (R0 : V → ℝ) (W : ℕ → V → ℝ)
    (hR : ∀ i, |R0 i| ≤ 1) (hW : ∀ k i, |W k i| ≤ G.budget c d i) :
    ∀ k i, |opinion G c d R0 W k i| ≤ 1 := by
  intro k
  induction k with
  | zero => exact hR
  | succ k ih =>
    intro i
    change |Δ G c d (opinion G c d R0 W k) i + W k i| ≤ 1
    have hδ := delta_abs_local G hG hcd (opinion G c d R0 W k) ih i
    have hw := hW k i
    unfold WDigraph.budget at hw
    have := abs_add_le (Δ G c d (opinion G c d R0 W k) i) (W k i)
    linarith

 theorem delta_iterate_abs_le {V : Type*} (G : WDigraph V) {c d M : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (_hd : d ≤ 1) (hM : 0 ≤ M)
    (f : V → ℝ) (hf : ∀ i, |f i| ≤ M) :
    ∀ k i, |(Δ G c d)^[k] f i| ≤ (1 - d)^k * M := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro i
    rw [Function.iterate_succ_apply']
    have h := delta_abs_le G hG hc hcd (mul_nonneg (pow_nonneg (by linarith) _) hM)
      ((Δ G c d)^[k] f) ih i
    convert h using 1; ring

 theorem native_opinion_mem {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A]
    [MeasurableSpace A] (P : MeasureTheory.Measure Ω) (S : GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ) (ω : Ω) (i : Fin (m+1)) :
    S.R ζ φ c d m k ω i ∈ Set.Icc (-1 : ℝ) 1 := by
  apply abs_le.mp
  apply opinion_abs_le_one (S.G m ω) (hS.valid m ω) hS.cd_le_one
  · intro j
    exact abs_le.mpr (hS.φ_mem _ _)
  · intro t j
    exact hS.signal_bound m t j ω

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clip_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clip lo hi x ∈ Icc lo hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

theorem clip_eq {lo hi x : ℝ} (hx : x ∈ Icc lo hi) : clip lo hi x = x := by
  simp [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_clip (lo hi : ℝ) : Continuous (clip lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clip_abs_sub_le {lo hi y : ℝ} (hy : y ∈ Icc lo hi) (x : ℝ) :
    |clip lo hi x - y| ≤ |x - y| := by
  by_cases hl : x < lo
  · rw [show clip lo hi x = lo by simp [clip, min_eq_right (hl.le.trans hy.1 |>.trans hy.2), max_eq_left hl.le]]
    rw [abs_of_nonpos (sub_nonpos.mpr hy.1), abs_of_nonpos (by linarith [hy.1, hy.2])]
    linarith
  · by_cases hh : hi < x
    · rw [show clip lo hi x = hi by simp [clip, min_eq_left hh.le, max_eq_right (hy.1.trans hy.2)]]
      rw [abs_of_nonneg (sub_nonneg.mpr hy.2), abs_of_nonneg (by linarith [hy.1, hy.2])]
      linarith
    · rw [clip_eq ⟨le_of_not_gt hl, le_of_not_gt hh⟩]

noncomputable def binaryRound (x : ℝ) : ℝ := if x ≤ (1/2 : ℝ) then 0 else 1

theorem binaryRound_mem (x : ℝ) : binaryRound x = 0 ∨ binaryRound x = 1 := by
  unfold binaryRound
  split_ifs <;> simp

theorem measurable_binaryRound : Measurable binaryRound := by
  unfold binaryRound
  exact measurable_const.piecewise (measurableSet_le measurable_id measurable_const) measurable_const

theorem binaryRound_abs_sub_le (x y : ℝ) (hy : y = 0 ∨ y = 1) :
    |binaryRound x - y| ≤ 2 * |x - y| := by
  rcases hy with rfl | rfl <;> unfold binaryRound <;> split_ifs with h <;>
    simp only [sub_zero, sub_self, abs_zero, zero_sub, abs_neg, abs_one] <;>
    have h1 := le_abs_self (x - 1) <;> have h2 := neg_le_abs (x - 1) <;>
    have h3 := le_abs_self x <;> have h4 := neg_le_abs x <;> linarith

noncomputable def canonicalMark {A : Type*} (x : Mark A) : Mark A :=
  (x.attr, clip (-1) 1 x.q, binaryRound x.s, x.deg,
    fun j => if j < x.deg then clip 0 1 (x.wt j) else 0)

theorem canonicalMark_mem {A : Type*} (x : Mark A) : canonicalMark x ∈ markSpace A := by
  refine ⟨clip_mem (by norm_num) _, binaryRound_mem _, ?_⟩
  intro j
  change (if j < x.deg then clip 0 1 (x.wt j) else 0) ∈ Icc (0:ℝ) 1
  split_ifs
  · exact clip_mem (by norm_num) _
  · norm_num

theorem rho_nonneg {A : Type*} [PseudoMetricSpace A] (x y : Mark A) : 0 ≤ ρ x y := by
  unfold ρ
  positivity

theorem kernelLipschitz_nonnegative_constant {A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} {K : ℝ} (h : KernelLipschitz ψ K) :
    KernelLipschitz ψ (max K 0) := by
  intro x hx y hy
  exact (h x hx y hy).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (rho_nonneg x y)))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

theorem measurable_countable_choice {Ω I X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] [MeasurableSpace X]
    (f : I → Ω → X) (hf : ∀ i, Measurable (f i)) (g : Ω → I) (hg : Measurable g) :
    Measurable (fun ω => f (g ω) ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × I => f p.2 p.1) hf).comp (measurable_id.prodMk hg)

theorem measurable_variable_sum {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (hf : ∀ r, Measurable (f r)) (n : Ω → ℕ) (hn : Measurable n) :
    Measurable (fun ω => ∑ r ∈ range (n ω), f r ω) := by
  apply measurable_countable_choice (fun k ω => ∑ r ∈ range k, f r ω) _ n hn
  intro k
  exact Finset.measurable_sum _ fun r _ => hf r

noncomputable def clippedOpinion {V : Type*} (G : WDigraph V) (c d : ℝ)
    (R0 : V → ℝ) (W : ℕ → V → ℝ) : ℕ → V → ℝ
  | 0 => fun i => clip (-1) 1 (R0 i)
  | k+1 => fun i => clip (-1) 1 (Δ G c d (clippedOpinion G c d R0 W k) i + clip (-1) 1 (W k i))

theorem clippedOpinion_mem {V : Type*} (G : WDigraph V) (c d : ℝ)
    (R0 : V → ℝ) (W : ℕ → V → ℝ) (k : ℕ) (i : V) :
    clippedOpinion G c d R0 W k i ∈ Icc (-1:ℝ) 1 := by
  cases k <;> exact clip_mem (by norm_num) _

theorem clippedOpinion_eq {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hcd : c+d ≤ 1) (R0 : V → ℝ) (W : ℕ → V → ℝ)
    (hR : ∀ i, |R0 i| ≤ 1) (hW : ∀ k i, |W k i| ≤ G.budget c d i) :
    ∀ k, clippedOpinion G c d R0 W k = opinion G c d R0 W k := by
  intro k
  induction k with
  | zero => funext i; exact clip_eq (abs_le.mp (hR i))
  | succ k ih =>
    funext i
    change clip (-1) 1 (Δ G c d (clippedOpinion G c d R0 W k) i + clip (-1) 1 (W k i)) = _
    rw [ih, clip_eq (abs_le.mp ((hW k i).trans (budget_le_one G hG hcd i)))]
    exact clip_eq (abs_le.mp (opinion_abs_le_one G hG hcd R0 W hR hW (k+1) i))

theorem clippedOpinion_measurable {Ω V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (G : Ω → WDigraph V) (c d : ℝ) (R0 : Ω → V → ℝ) (W : Ω → ℕ → V → ℝ)
    (hdeg : ∀ i, Measurable (fun ω => (G ω).deg i))
    (hnbr : ∀ i r, Measurable (fun ω => (G ω).nbr i r))
    (hwt : ∀ i r, Measurable (fun ω => (G ω).wt i r))
    (hR : ∀ i, Measurable (fun ω => R0 ω i))
    (hW : ∀ k i, Measurable (fun ω => W ω k i)) :
    ∀ k i, Measurable (fun ω => clippedOpinion (G ω) c d (R0 ω) (W ω) k i) := by
  intro k
  induction k with
  | zero => intro i; exact (continuous_clip (-1) 1).measurable.comp (hR i)
  | succ k ih =>
    intro i
    change Measurable (fun ω => clip (-1) 1
      ((∑ r ∈ range ((G ω).deg i), (G ω).wt i r *
        clippedOpinion (G ω) c d (R0 ω) (W ω) k ((G ω).nbr i r)) +
        (1-c-d) * clippedOpinion (G ω) c d (R0 ω) (W ω) k i + clip (-1) 1 (W ω k i)))
    apply (continuous_clip (-1) 1).measurable.comp
    apply Measurable.add
    · apply Measurable.add
      · apply measurable_variable_sum _ _ _ (hdeg i)
        intro r
        exact (hwt i r).mul (measurable_countable_choice _ ih _ (hnbr i r))
      · exact measurable_const.mul (ih i)
    · exact (continuous_clip (-1) 1).measurable.comp (hW k i)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

theorem measurable_canonicalMark {A : Type*} [MeasurableSpace A] :
    Measurable (canonicalMark : Mark A → Mark A) := by
  have ha : Measurable (fun x : Mark A => x.attr) := by unfold Mark.attr; fun_prop
  have hq : Measurable (fun x : Mark A => clip (-1) 1 x.q) :=
    (continuous_clip (-1) 1).measurable.comp (by unfold Mark.q; fun_prop)
  have hs : Measurable (fun x : Mark A => binaryRound x.s) :=
    measurable_binaryRound.comp (by unfold Mark.s; fun_prop)
  have hd : Measurable (fun x : Mark A => x.deg) := by unfold Mark.deg; fun_prop
  have hw : Measurable (fun x : Mark A => fun j => if j < x.deg then clip 0 1 (x.wt j) else 0) := by
    apply measurable_pi_lambda
    intro j
    exact ((continuous_clip 0 1).measurable.comp (by unfold Mark.wt; fun_prop)).piecewise
      (measurableSet_lt measurable_const hd) measurable_const
  exact ha.prodMk (hq.prodMk (hs.prodMk (hd.prodMk hw)))

def truncatedWeight {A : Type*} (x : Mark A) (j : ℕ) : ℝ :=
  if j < x.deg then x.wt j else 0

theorem weight_difference_sum {A : Type*} (x y : Mark A) :
    (∑' j, |truncatedWeight x j - truncatedWeight y j|) =
      ∑ j ∈ range (max x.deg y.deg), |truncatedWeight x j - truncatedWeight y j| := by
  apply tsum_eq_sum
  intro j hj
  have hx : ¬ j < x.deg := by simp only [Finset.mem_range] at hj; omega
  have hy : ¬ j < y.deg := by simp only [Finset.mem_range] at hj; omega
  simp [truncatedWeight, hx, hy]

theorem canonical_weight_distance {A : Type*} (x y : Mark A) (hy : y ∈ markSpace A) (j : ℕ) :
    |truncatedWeight (canonicalMark x) j - truncatedWeight y j| ≤
      |truncatedWeight x j - truncatedWeight y j| := by
  have hyv : truncatedWeight y j ∈ Icc (0:ℝ) 1 := by
    unfold truncatedWeight
    split_ifs
    · exact hy.2.2 j
    · norm_num
  by_cases hj : j < x.deg
  · change j < x.2.2.2.1 at hj
    simpa [truncatedWeight, canonicalMark, Mark.deg, Mark.wt, hj] using
      clip_abs_sub_le hyv (x.wt j)
  · change ¬j < x.2.2.2.1 at hj
    simp [truncatedWeight, canonicalMark, Mark.deg, Mark.wt, hj]

theorem canonical_rho_le {A : Type*} [PseudoMetricSpace A] (x y : Mark A)
    (hy : y ∈ markSpace A) : ρ (canonicalMark x) y ≤ 2 * ρ x y := by
  have hq := clip_abs_sub_le hy.1 x.q
  have hs := binaryRound_abs_sub_le x.s y.s hy.2.1
  have hw : (∑' j, |truncatedWeight (canonicalMark x) j - truncatedWeight y j|) ≤
      ∑' j, |truncatedWeight x j - truncatedWeight y j| := by
    rw [weight_difference_sum, weight_difference_sum]
    change (∑ j ∈ range (max x.deg y.deg), _) ≤ _
    exact sum_le_sum fun j _ => canonical_weight_distance x y hy j
  have hn : 0 ≤ ∑' j, |truncatedWeight x j - truncatedWeight y j| := tsum_nonneg fun _ => abs_nonneg _
  change dist x.attr y.attr + |clip (-1) 1 x.q-y.q| + |binaryRound x.s-y.s| +
    |(x.deg:ℝ)-y.deg| + (∑' j, |truncatedWeight (canonicalMark x) j-truncatedWeight y j|) ≤ _
  change _ ≤ 2 * (dist x.attr y.attr + |x.q-y.q| + |x.s-y.s| + |(x.deg:ℝ)-y.deg| +
    ∑' j, |truncatedWeight x j-truncatedWeight y j|)
  have hd := dist_nonneg (x := x.attr) (y := y.attr)
  have ha := abs_nonneg ((x.deg:ℝ)-y.deg)
  have hb := abs_nonneg (x.q-y.q)
  linarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

abbrev Noise := Option ℕ × ℕ → ℝ
noncomputable def uniformUnit : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
instance uniformUnit_probability : IsProbabilityMeasure uniformUnit := by
  constructor
  simp [uniformUnit]
noncomputable def noiseLaw : Measure Noise := Measure.infinitePi (fun _ : Option ℕ × ℕ => uniformUnit)
instance noiseLaw_probability : IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  infer_instance

noncomputable def canonicalGraph {A : Type*} (H : LimGraph A) : WDigraph ℕ :=
  LimGraph.toWDigraph (H.1, fun i => canonicalMark (H.2 i))

noncomputable def auxiliaryOpinion {A : Type*} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (H : LimGraph A) (u : Noise) (k i : ℕ) : ℝ :=
  clippedOpinion (canonicalGraph H) c d
    (fun j => φ (canonicalMark (H.2 j)) (u (none,j)))
    (fun t j => ζ (canonicalMark (H.2 j)) (u (some t,j))) k i

theorem auxiliaryOpinion_measurable {A : Type*} [MeasurableSpace A]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k i : ℕ) :
    Measurable (fun p : LimGraph A × Noise => auxiliaryOpinion ζ φ c d p.1 p.2 k i) := by
  apply clippedOpinion_measurable
  · intro j
    change Measurable (fun p : LimGraph A × Noise => (p.1.2 j).deg)
    unfold Mark.deg
    fun_prop
  · intro j r
    change Measurable (fun p : LimGraph A × Noise => p.1.1 j r)
    fun_prop
  · intro j r
    change Measurable (fun p : LimGraph A × Noise => (canonicalMark (p.1.2 j)).wt r)
    have hm : Measurable (fun p : LimGraph A × Noise => canonicalMark (p.1.2 j)) :=
      measurable_canonicalMark.comp (by fun_prop)
    exact (by unfold Mark.wt; fun_prop : Measurable (fun x : Mark A => x.wt r)).comp hm
  · intro j
    exact hφ.comp ((measurable_canonicalMark.comp (by fun_prop)).prodMk (by fun_prop))
  · intro t j
    exact hζ.comp ((measurable_canonicalMark.comp (by fun_prop)).prodMk (by fun_prop))

theorem auxiliaryOpinion_mem {A : Type*} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (H : LimGraph A) (u : Noise) (k i : ℕ) :
    auxiliaryOpinion ζ φ c d H u k i ∈ Icc (-1:ℝ) 1 :=
  clippedOpinion_mem _ _ _ _ _ _ _

noncomputable def auxiliaryTrajectory {A : Type*} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (k : ℕ) (p : LimGraph A × Noise) : Fin (k+1) → ℝ :=
  fun r => auxiliaryOpinion ζ φ c d p.1 p.2 r 0

theorem auxiliaryTrajectory_measurable {A : Type*} [MeasurableSpace A]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) :
    Measurable (auxiliaryTrajectory ζ φ c d k) :=
  measurable_pi_lambda _ fun r => auxiliaryOpinion_measurable ζ φ hζ hφ c d r 0

noncomputable def auxiliaryTrajectoryLaw {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) :
    ProbabilityMeasure (Fin (k+1) → ℝ) :=
  ⟨(μ.prod noiseLaw).map (auxiliaryTrajectory ζ φ c d k),
    Measure.isProbabilityMeasure_map (auxiliaryTrajectory_measurable ζ φ hζ hφ c d k).aemeasurable⟩

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω)
variable (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_mark_measurable (m : ℕ) (i : Fin (m+1)) : Measurable (S.mark m i) := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have ha : Measurable (fun ω => S.Y m i ω) := hg.snd.snd.snd.eval
  have hd : Measurable (fun ω => (S.G m ω).deg i) := hg.fst.eval
  have hw : ∀ j, Measurable (fun ω => (S.G m ω).wt i j) := fun _ => hg.snd.snd.fst.eval.eval
  have hc : Measurable (fun ω => fun j => if j < (S.G m ω).deg i then (S.G m ω).wt i j else 0) := by
    apply measurable_pi_lambda
    intro j
    exact (hw j).piecewise (measurableSet_lt measurable_const hd) measurable_const
  exact ha.fst.prodMk (ha.snd.fst.prodMk (ha.snd.snd.prodMk (hd.prodMk hc)))

theorem native_R_measurable (m k : ℕ) (i : Fin (m+1)) :
    Measurable (fun ω => S.R ζ φ c d m k ω i) := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have hc : Measurable (fun ω => clippedOpinion (S.G m ω) c d (S.R0 φ m ω)
      (fun t j => S.W ζ m t j ω) k i) := by
    apply clippedOpinion_measurable
    · intro j; exact hg.fst.eval
    · intro j r; exact hg.snd.fst.eval.eval
    · intro j r; exact hg.snd.snd.fst.eval.eval
    · intro j
      exact hS.measurable_φ.comp ((native_mark_measurable P S 𝓖 ζ φ c d hS m j).prodMk
        (hS.measurable_unif m (none,j)))
    · intro t j
      exact hS.measurable_ζ.comp ((native_mark_measurable P S 𝓖 ζ φ c d hS m j).prodMk
        (hS.measurable_unif m (some t,j)))
  have he : (fun ω => clippedOpinion (S.G m ω) c d (S.R0 φ m ω)
      (fun t j => S.W ζ m t j ω) k i) = (fun ω => S.R ζ φ c d m k ω i) := by
    funext ω
    exact congrFun (clippedOpinion_eq (S.G m ω) (hS.valid m ω) hS.cd_le_one _ _
      (fun j => abs_le.mpr (hS.φ_mem _ _)) (fun t j => hS.signal_bound m t j ω) k) i
  rwa [he] at hc

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

noncomputable def finiteVertexNoiseLaw (m : ℕ) : Measure (Option ℕ × Fin (m+1) → ℝ) :=
  Measure.infinitePi (fun _ : Option ℕ × Fin (m+1) => uniformUnit)

instance finiteVertexNoiseLaw_probability (m : ℕ) : IsProbabilityMeasure (finiteVertexNoiseLaw m) := by
  unfold finiteVertexNoiseLaw
  infer_instance

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω)
variable (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_noise_hasLaw (m : ℕ) :
    HasLaw (fun ω p => S.unif m p ω) (finiteVertexNoiseLaw m) P := by
  exact iIndepFun.hasLaw_infinitePi (hS.unif_law m) (hS.unif_iIndep m)
    (measurable_pi_lambda _ (hS.measurable_unif m)).aemeasurable

theorem native_noise_indep_struct_function {X : Type*} [MeasurableSpace X]
    (m : ℕ) (T : Ω → X) (hT : Measurable[𝓖 m] T) :
    IndepFun (fun ω p => S.unif m p ω) T P := by
  exact indep_of_indep_of_le_right (hS.unif_indep_struct m) hT.comap_le

theorem native_struct_noise_jointLaw [IsProbabilityMeasure P] {X : Type*} [MeasurableSpace X]
    (m : ℕ) (T : Ω → X) (hT : Measurable[𝓖 m] T) (ν : Measure X) (hLaw : HasLaw T ν P) :
    HasLaw (fun ω => (T ω, fun p => S.unif m p ω)) (ν.prod (finiteVertexNoiseLaw m)) P := by
  exact (native_noise_indep_struct_function P S 𝓖 ζ φ c d hS m T hT).symm.hasLaw_prod
    hLaw (native_noise_hasLaw P S 𝓖 ζ φ c d hS m)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

abbrev NativeGraphData (A : Type*) (m : ℕ) :=
  (Fin (m+1) → ℕ) × (Fin (m+1) → ℕ → Fin (m+1)) × (Fin (m+1) → ℕ → ℝ) ×
    (Fin (m+1) → A × ℝ × ℝ)

noncomputable def uniformVertex (m : ℕ) : Measure (Fin (m+1)) :=
  (PMF.uniformOfFintype (Fin (m+1))).toMeasure

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

theorem native_index_indep_graph_noise {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ) :
    IndepFun (S.I m) (fun ω => (S.graphData m ω, fun p => S.unif m p ω)) P := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have hgl : HasLaw (S.graphData m) (P.map (S.graphData m)) P := ⟨hg.aemeasurable, rfl⟩
  have hig : IndepFun (S.I m) (S.graphData m) P :=
    (hS.indep_I m).comp measurable_id measurable_snd
  have higl := hig.hasLaw_prod (hS.I_unif m) hgl
  have htotal := native_struct_noise_jointLaw P S 𝓖 ζ φ c d hS m
    (fun ω => (S.I m ω, S.graphData m ω))
    ((hS.measurable_I m).prodMk (hS.measurable_graph m)) _ higl
  have hgn := native_struct_noise_jointLaw P S 𝓖 ζ φ c d hS m
    (S.graphData m) (hS.measurable_graph m) _ hgl
  have hassoc : HasLaw
      (MeasurableEquiv.prodAssoc :
        (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ) →
        Fin (m+1) × (NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ)))
      ((uniformVertex m).prod ((P.map (S.graphData m)).prod (finiteVertexNoiseLaw m)))
      (((uniformVertex m).prod (P.map (S.graphData m))).prod (finiteVertexNoiseLaw m)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable.aemeasurable, Measure.prodAssoc_prod⟩
  exact (indepFun_iff_hasLaw_prodMk_prod (hS.I_unif m) hgn).2 (hassoc.comp htotal)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

def IsCoupling {X : Type*} [MeasurableSpace X]
    (π : Measure (X × X)) (μ ν : Measure X) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν

theorem transport_le_coupling {X : Type*} [MeasurableSpace X]
    (c : X → X → ℝ≥0∞) {μ ν : Measure X} {π : Measure (X × X)}
    (hπ : IsCoupling π μ ν) :
    RWPI.SqrtLasso.transportCost c μ ν ≤ ∫⁻ z, c z.1 z.2 ∂π := by
  exact iInf_le_of_le π (iInf_le_of_le hπ le_rfl)

theorem transport_exists_coupling_lt {X : Type*} [MeasurableSpace X]
    (c : X → X → ℝ≥0∞) {μ ν : Measure X} {b : ℝ≥0∞}
    (h : RWPI.SqrtLasso.transportCost c μ ν < b) :
    ∃ π, IsCoupling π μ ν ∧ (∫⁻ z, c z.1 z.2 ∂π) < b := by
  simp only [RWPI.SqrtLasso.transportCost, iInf_lt_iff] at h
  rcases h with ⟨π, hπ, hc⟩
  exact ⟨π, hπ, hc⟩

theorem coupling_prod {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν := by
  exact ⟨inferInstance, by simp, by simp⟩

theorem coupling_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ ν : Measure X} {π : Measure (X × X)} (hπ : IsCoupling π μ ν)
    {f g : X → Y} (hf : Measurable f) (hg : Measurable g) :
    IsCoupling (π.map (fun z => (f z.1, g z.2))) (μ.map f) (ν.map g) := by
  have hp : Measurable (fun z : X × X => (f z.1, g z.2)) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  let : IsProbabilityMeasure π := hπ.1
  refine ⟨π.isProbabilityMeasure_map hp.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hp]
    change π.map (f ∘ Prod.fst) = μ.map f
    rw [← Measure.map_map hf measurable_fst, hπ.2.1]
  · rw [Measure.map_map measurable_snd hp]
    change π.map (g ∘ Prod.snd) = ν.map g
    rw [← Measure.map_map hg measurable_snd, hπ.2.2]

theorem transport_map_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (cX : X → X → ℝ≥0∞) (cY : Y → Y → ℝ≥0∞)
    (hcY : Measurable (Function.uncurry cY)) (μ ν : Measure X)
    {f g : X → Y} (hf : Measurable f) (hg : Measurable g)
    (hcost : ∀ x y, cY (f x) (g y) ≤ cX x y) :
    RWPI.SqrtLasso.transportCost cY (μ.map f) (ν.map g) ≤
      RWPI.SqrtLasso.transportCost cX μ ν := by
  refine le_iInf fun π => le_iInf fun hπ => ?_
  have hp : Measurable (fun z : X × X => (f z.1, g z.2)) :=
    (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)
  calc
    RWPI.SqrtLasso.transportCost cY (μ.map f) (ν.map g) ≤
        ∫⁻ z, cY z.1 z.2 ∂(π.map (fun z => (f z.1, g z.2))) :=
      transport_le_coupling cY (coupling_map hπ hf hg)
    _ = ∫⁻ z, cY (f z.1) (g z.2) ∂π := lintegral_map hcY hp
    _ ≤ ∫⁻ z, cX z.1 z.2 ∂π := lintegral_mono fun z => hcost z.1 z.2

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem finite_test_abs_sum_probability {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (P : Measure Ω) (f : I → ℕ → Ω → ℝ) (c : I → ℝ)
    (hf : ∀ i, TendstoInMeasure P (f i) atTop (fun _ => c i))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ∑ i, |f i n ω - c i|}) atTop (𝓝 0) := by
  classical
  let N : ℝ := Fintype.card I
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let t : ℝ := ε / (N + 1)
  have ht : 0 < t := div_pos hε (by linarith)
  have hNt : N * t < ε := by
    dsimp [t]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < N + 1)).2
    nlinarith
  have hsub : ∀ n, {ω | ε ≤ ∑ i, |f i n ω - c i|} ⊆
      ⋃ i : I, {ω | t ≤ |f i n ω - c i|} := by
    intro n ω hω
    by_contra hnot
    have hall : ∀ i, |f i n ω - c i| < t := by
      intro i
      by_contra hi
      exact hnot (mem_iUnion.mpr ⟨i, le_of_not_gt hi⟩)
    have hsum : (∑ i, |f i n ω - c i|) ≤ N * t := by
      calc
        (∑ i, |f i n ω - c i|) ≤ ∑ _ : I, t :=
          Finset.sum_le_sum fun i _ => (hall i).le
        _ = N * t := by simp [N]
    exact (not_le_of_gt (hsum.trans_lt hNt)) hω
  have htest : ∀ i, Tendsto (fun n => P {ω | t ≤ |f i n ω - c i|}) atTop (𝓝 0) := by
    intro i
    simpa only [Real.dist_eq] using (tendstoInMeasure_iff_dist.1 (hf i)) t ht
  have hsumlim : Tendsto (fun n => ∑ i, P {ω | t ≤ |f i n ω - c i|}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => htest i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumlim (fun _ => bot_le)
  intro n
  exact (measure_mono (hsub n)).trans (measure_iUnion_fintype_le P _)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem integral_abs_condExp_sub_const_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ) :
    (∫ ω, |P[f | m] ω - c| ∂P) ≤ ∫ ω, |f ω - c| ∂P := by
  have he : P[(fun ω => f ω - c) | m] =ᵐ[P] (fun ω => P[f | m] ω - c) := by
    simpa only [Pi.sub_def, condExp_const hm c] using
      (condExp_sub hf (integrable_const c) m)
  calc
    (∫ ω, |P[f | m] ω - c| ∂P) = ∫ ω, |P[(fun ω => f ω - c) | m] ω| ∂P :=
      integral_congr_ae (he.fun_comp abs).symm
    _ ≤ ∫ ω, |f ω - c| ∂P := integral_abs_condExp_le _

theorem in_measure_of_integral_abs_sub_const {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ)
    (hf : ∀ n, Integrable (f n) P) (c : ℝ)
    (hlim : Tendsto (fun n => ∫ ω, |f n ω - c| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => c) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1)
    (by norm_num) (by simp) (fun n => (hf n).aestronglyMeasurable) aestronglyMeasurable_const
  have heq : ∀ n, eLpNorm (f n - fun _ => c) 1 P =
      ENNReal.ofReal (∫ ω, |f n ω - c| ∂P) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hf n).sub (integrable_const c))]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  simp_rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim

theorem conditional_test_in_measure {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ n, m n ≤ mΩ) (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) P)
    (c : ℝ) (hlim : Tendsto (fun n => ∫ ω, |f n ω - c| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => P[f n | m n]) atTop (fun _ => c) := by
  apply in_measure_of_integral_abs_sub_const P _ (fun _ => integrable_condExp) c
  exact squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun n => integral_abs_condExp_sub_const_le P (m n) (hm n) (f n) (hf n) c) hlim

theorem conditional_test_in_measure_of_ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ n, m n ≤ mΩ) (f g : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) P)
    (hge : ∀ n, g n =ᵐ[P] P[f n | m n]) (c : ℝ)
    (hlim : Tendsto (fun n => ∫ ω, |f n ω - c| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P g atTop (fun _ => c) :=
  TendstoInMeasure.congr_left (fun n => (hge n).symm) (conditional_test_in_measure P m hm f hf c hlim)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

theorem independent_index_condExp {Ω I : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (J : Ω → I) (hJ : Measurable[mΩ] J)
    (hindep : Indep (MeasurableSpace.comap J inferInstance) m P)
    (g : I → Ω → ℝ) (hgm : ∀ i, StronglyMeasurable[m] (g i))
    (hgi : ∀ i, Integrable (g i) P) :
    P[(fun ω => g (J ω) ω) | m] =ᵐ[P]
      (fun ω => ∑ i, g i ω * ∫ a, ({a | J a = i}.indicator (fun _ => (1 : ℝ))) a ∂P) := by
  classical
  let a : I → Ω → ℝ := fun i => {ω | J ω = i}.indicator (fun _ => 1)
  let v : I → Ω → ℝ := fun i => g i * a i
  have hs : ∀ i, MeasurableSet[mΩ] {ω | J ω = i} := fun i => hJ (measurableSet_singleton i)
  have ha : ∀ i, Integrable (a i) P := fun i => (integrable_const 1).indicator (hs i)
  have hv : ∀ i, Integrable (v i) P := by
    intro i
    have he : v i = {ω | J ω = i}.indicator (g i) := by
      funext ω
      by_cases h : J ω = i <;> simp [v, a, h]
    rw [he]
    exact (hgi i).indicator (hs i)
  have ha_cond : ∀ i, P[a i | m] =ᵐ[P] (fun _ => ∫ ω, a i ω ∂P) := by
    intro i
    have hJ' : Measurable[MeasurableSpace.comap J inferInstance] J :=
      Measurable.of_comap_le le_rfl
    have hma : StronglyMeasurable[MeasurableSpace.comap J inferInstance] (a i) :=
      stronglyMeasurable_const.indicator (hJ' (measurableSet_singleton i))
    exact condExp_indep_eq hJ.comap_le hm hma hindep
  have hterm : ∀ i, P[v i | m] =ᵐ[P] (fun ω => g i ω * ∫ a', a i a' ∂P) := by
    intro i
    exact (condExp_mul_of_stronglyMeasurable_left (hgm i) (hv i) (ha i)).trans
      (Filter.EventuallyEq.rfl.mul (ha_cond i))
  have hsel : (fun ω => g (J ω) ω) = ∑ i, v i := by
    funext ω
    simp [v, a, Finset.sum_apply, Set.indicator, eq_comm]
  rw [hsel]
  have hsum := condExp_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hv i) m
  filter_upwards [hsum, ae_all_iff.2 hterm] with ω hsumω htermω
  simpa only [Finset.sum_apply, htermω] using hsumω

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem uniform_index_indicator_integral {Ω I : Type*} [MeasurableSpace Ω]
    [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) (J : Ω → I) (hJ : Measurable J)
    (hLaw : HasLaw J (PMF.uniformOfFintype I).toMeasure P) (i : I) :
    (∫ a, ({a | J a = i}.indicator (fun _ => (1 : ℝ))) a ∂P) =
      (Fintype.card I : ℝ)⁻¹ := by
  have hmass : P {a | J a = i} = (Fintype.card I : ℝ≥0∞)⁻¹ := by
    calc
      P {a | J a = i} = (P.map J) {i} := (Measure.map_apply hJ (measurableSet_singleton i)).symm
      _ = (Fintype.card I : ℝ≥0∞)⁻¹ := by
        rw [hLaw.map_eq, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
          PMF.uniformOfFintype_apply]
  have hs : MeasurableSet {a | J a = i} := hJ (measurableSet_singleton i)
  rw [integral_indicator_const 1 hs]
  simp [measureReal_def, hmass]

theorem uniform_index_condExp {Ω I : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (J : Ω → I) (hJ : Measurable[mΩ] J)
    (hindep : Indep (MeasurableSpace.comap J inferInstance) m P)
    (hLaw : HasLaw J (PMF.uniformOfFintype I).toMeasure P)
    (g : I → Ω → ℝ) (hgm : ∀ i, StronglyMeasurable[m] (g i))
    (hgi : ∀ i, Integrable (g i) P) :
    P[(fun ω => g (J ω) ω) | m] =ᵐ[P]
      (fun ω => (Fintype.card I : ℝ)⁻¹ * ∑ i, g i ω) := by
  let : MeasurableSpace Ω := mΩ
  have h := independent_index_condExp P m hm J hJ hindep g hgm hgi
  filter_upwards [h] with ω hω
  rw [hω]
  simp_rw [uniform_index_indicator_integral P J hJ hLaw]
  rw [← Finset.sum_mul, mul_comm]

theorem uniform_index_condExp_smaller {Ω I : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) [IsFiniteMeasure P] (m₀ m₁ : MeasurableSpace Ω)
    (h01 : m₀ ≤ m₁) (h1 : m₁ ≤ mΩ)
    (J : Ω → I) (hJ : Measurable[mΩ] J)
    (hindep : Indep (MeasurableSpace.comap J inferInstance) m₁ P)
    (hLaw : HasLaw J (PMF.uniformOfFintype I).toMeasure P)
    (g : I → Ω → ℝ) (hgm : ∀ i, StronglyMeasurable[m₁] (g i))
    (hgi : ∀ i, Integrable (g i) P) :
    P[(fun ω => g (J ω) ω) | m₀] =ᵐ[P]
      P[(fun ω => (Fintype.card I : ℝ)⁻¹ * ∑ i, g i ω) | m₀] := by
  let : MeasurableSpace Ω := mΩ
  have h := uniform_index_condExp P m₁ h1 J hJ hindep hLaw g hgm hgi
  exact (condExp_condExp_of_le h01 h1).symm.trans (condExp_congr_ae h)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

theorem conditional_law_support {Ω B X : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsFiniteMeasure P] (T : Ω → B) (Y : Ω → X)
    (hT : AEMeasurable T P) (hY : AEMeasurable Y P)
    (p : X → Prop) (hp : MeasurableSet {x | p x}) (h : ∀ᵐ ω ∂P, p (Y ω)) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂condDistrib Y T P (T ω), p x := by
  have hm : ∀ᵐ x ∂P.map Y, p x := (ae_map_iff hY hp).2 h
  rw [← condDistrib_comp_map hT hY] at hm
  exact ae_of_ae_map hT (Measure.ae_ae_of_ae_comp hm)

theorem conditional_uniform_test_identity {Ω I B X : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace B] [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (J : Ω → I) (hJ : Measurable[mΩ] J)
    (hindep : Indep (MeasurableSpace.comap J inferInstance) m P)
    (hLaw : HasLaw J (PMF.uniformOfFintype I).toMeasure P)
    (T : Ω → B) (hT : Measurable[m] T) (Z : I → Ω → X)
    (hY : Measurable[mΩ] (fun ω => Z (J ω) ω))
    (f : X → ℝ) (hf : StronglyMeasurable f)
    (hfm : ∀ i, StronglyMeasurable[m] (fun ω => f (Z i ω)))
    (hfi : ∀ i, Integrable (fun ω => f (Z i ω)) P)
    (hfY : Integrable (fun ω => f (Z (J ω) ω)) P) :
    (fun ω => ∫ x, f x ∂condDistrib (fun ω => Z (J ω) ω) T P (T ω)) =ᵐ[P]
      P[(fun ω => (Fintype.card I : ℝ)⁻¹ * ∑ i, f (Z i ω)) |
        MeasurableSpace.comap T inferInstance] := by
  let : MeasurableSpace Ω := mΩ
  have hc := condExp_ae_eq_integral_condDistrib (hT.mono hm le_rfl) hY.aemeasurable hf hfY
  have hu := uniform_index_condExp_smaller P (MeasurableSpace.comap T inferInstance) m
    hT.comap_le hm J hJ hindep hLaw (fun i ω => f (Z i ω)) hfm hfi
  exact hc.symm.trans hu

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem native_conditional_kernel_test_identity {Ω A X : Type*} [mΩ : MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A]
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ)
    (K : Fin (m+1) → NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) → X)
    (hK : ∀ i, Measurable (K i)) (f : X → ℝ) (hf : StronglyMeasurable f)
    (hfi : ∀ i, Integrable
      (fun ω => f (K i (S.graphData m ω, fun p => S.unif m p ω))) P)
    (hfr : Integrable
      (fun ω => f (K (S.I m ω) (S.graphData m ω, fun p => S.unif m p ω))) P) :
    (fun ω => ∫ x, f x ∂condDistrib
      (fun ω' => K (S.I m ω') (S.graphData m ω', fun p => S.unif m p ω'))
      (S.attrs m) P (S.attrs m ω)) =ᵐ[P]
    P[(fun ω => (Fintype.card (Fin (m+1)) : ℝ)⁻¹ *
      ∑ i, f (K i (S.graphData m ω, fun p => S.unif m p ω))) | S.𝓐 m] := by
  let D : Ω → NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) :=
    fun ω => (S.graphData m ω, fun p => S.unif m p ω)
  let M : MeasurableSpace Ω := MeasurableSpace.comap D inferInstance
  let : MeasurableSpace Ω := mΩ
  have hD : Measurable D := ((hS.measurable_graph m).mono (hS.le m) le_rfl).prodMk
    (measurable_pi_lambda _ (hS.measurable_unif m))
  have hDM : Measurable[M] D := Measurable.of_comap_le le_rfl
  have hT : Measurable[M] (S.attrs m) := hDM.fst.snd.snd.snd
  have hI : Measurable (S.I m) := (hS.measurable_I m).mono (hS.le m) le_rfl
  have hY : Measurable (fun ω => K (S.I m ω) (D ω)) :=
    measurable_countable_choice (fun i ω => K i (D ω)) (fun i => (hK i).comp hD) (S.I m) hI
  exact conditional_uniform_test_identity P M hD.comap_le (S.I m) hI
    (native_index_indep_graph_noise P S 𝓖 ζ φ c d hS m) (hS.I_unif m)
    (S.attrs m) hT (fun i ω => K i (D ω)) hY f hf
    (fun i => (hf.measurable.comp ((hK i).comp hDM)).stronglyMeasurable) hfi hfr

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

theorem independent_noise_integral {Ω X U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace U] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure U) [IsProbabilityMeasure ν] (T : Ω → X) (N : Ω → U)
    (hT : Measurable T) (hN : HasLaw N ν P) (hI : IndepFun T N P)
    (F : X × U → ℝ) (hF : Measurable F) (hi : Integrable F ((P.map T).prod ν)) :
    (∫ ω,F (T ω,N ω) ∂P) = ∫ ω,(∫ u,F (T ω,u) ∂ν) ∂P := by
  have hL := hI.hasLaw_prod (show HasLaw T (P.map T) P from ⟨hT.aemeasurable,rfl⟩) hN
  have he := hL.integral_comp hF.aestronglyMeasurable
  rw [integral_prod F hi] at he
  have hm := hF.stronglyMeasurable.integral_prod_right' (ν := ν)
  rw [integral_map hT.aemeasurable hm.aestronglyMeasurable] at he
  exact he

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

theorem product_coordinate_integral {I X : Type*} [Fintype I] [MeasurableSpace X]
    (π : I → Measure X) [∀ i, IsProbabilityMeasure (π i)] (i : I)
    (f : X → ℝ) (hf : Measurable f) :
    ∫ z : I → X, f (z i) ∂Measure.pi π = ∫ x, f x ∂π i := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable,
    (measurePreserving_eval π i).map_eq]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

theorem finite_signal_sample_law {I J : Type*} [Fintype I]
    (e : I → J) (he : Function.Injective e) (f : I → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
    HasLaw (fun u : J → ℝ => fun i => f i (u (e i)))
      (Measure.pi (fun i => uniformUnit.map (f i)))
      (Measure.infinitePi (fun _ : J => uniformUnit)) := by
  have hi : iIndepFun (fun j (u : J → ℝ) => u j)
      (Measure.infinitePi (fun _ : J => uniformUnit)) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hi' := (hi.precomp he).comp f hf
  apply hi'.hasLaw_pi
  intro i
  have hu : HasLaw (fun u : J → ℝ => u (e i)) uniformUnit
      (Measure.infinitePi (fun _ : J => uniformUnit)) :=
    (measurePreserving_eval_infinitePi (fun _ : J => uniformUnit) (e i)).hasLaw
  have hfLaw : HasLaw (f i) (uniformUnit.map (f i)) uniformUnit :=
    ⟨(hf i).aemeasurable,rfl⟩
  exact hfLaw.comp hu

abbrev SignalSlot (V : Type*) (k : ℕ) := Option (Fin k) × V

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Set

theorem inBall_finite {V : Type*} (G : WDigraph V) (v : V) : ∀ k, (inBall G v k).Finite := by
  intro k
  induction k with
  | zero => exact finite_singleton v
  | succ k ih =>
    change (inBall G v k ∪ {u | ∃ w ∈ inBall G v k, ∃ r < G.deg w, G.nbr w r = u}).Finite
    apply ih.union
    have hf : (⋃ w ∈ inBall G v k, (G.nbr w) '' {r : ℕ | r < G.deg w}).Finite :=
      ih.biUnion fun w _ => (finite_Iio (G.deg w)).image (G.nbr w)
    convert hf using 1
    ext u
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    simp only [exists_prop]

theorem root_mem_inBall {V : Type*} (G : WDigraph V) (v : V) : ∀ k, v ∈ inBall G v k := by
  intro k
  induction k with
  | zero => exact rfl
  | succ k ih => exact Or.inl ih

theorem inBall_mono {V : Type*} (G : WDigraph V) (v : V) : Monotone (inBall G v) := by
  apply monotone_nat_of_le_succ
  intro k
  exact fun _ h => Or.inl h

theorem neighbor_mem_inBall {V : Type*} (G : WDigraph V) (v w : V) (k r : ℕ)
    (hw : w ∈ inBall G v k) (hr : r < G.deg w) : G.nbr w r ∈ inBall G v (k+1) :=
  Or.inr ⟨w, hw, r, hr, rfl⟩

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Set

theorem inBall_from_member {V : Type*} (G : WDigraph V) {v w : V} {j : ℕ}
    (hw : w ∈ inBall G v j) : ∀ k, inBall G w k ⊆ inBall G v (j+k) := by
  intro k
  induction k with
  | zero => simpa [inBall] using hw
  | succ k ih =>
    intro x hx
    rcases hx with hx | ⟨y, hy, r, hr, rfl⟩
    · exact inBall_mono G v (by omega) (ih hx)
    · simpa [Nat.add_assoc] using neighbor_mem_inBall G v y (j+k) r (ih hy) hr

theorem inBall_neighbor_subset {V : Type*} (G : WDigraph V) (v : V) {r : ℕ}
    (hr : r < G.deg v) (k : ℕ) : inBall G (G.nbr v r) k ⊆ inBall G v (k+1) := by
  have hm := neighbor_mem_inBall G v v 0 r (root_mem_inBall G v 0) hr
  simpa [Nat.add_comm] using inBall_from_member G hm k

theorem clippedOpinion_locality {V : Type*} (G : WDigraph V) (c d : ℝ)
    (f g : V → ℝ) (W Z : ℕ → V → ℝ) : ∀ k v,
    (∀ i ∈ inBall G v k, f i = g i) →
    (∀ t < k, ∀ i ∈ inBall G v k, W t i = Z t i) →
    clippedOpinion G c d f W k v = clippedOpinion G c d g Z k v := by
  intro k
  induction k with
  | zero =>
    intro v hf _
    change clip (-1) 1 (f v) = clip (-1) 1 (g v)
    rw [hf v (root_mem_inBall G v 0)]
  | succ k ih =>
    intro v hf hW
    have hc : clippedOpinion G c d f W k v = clippedOpinion G c d g Z k v :=
      ih v (fun i hi => hf i (inBall_mono G v (by omega) hi))
        (fun t ht i hi => hW t (by omega) i (inBall_mono G v (by omega) hi))
    have hn : ∀ r < G.deg v, clippedOpinion G c d f W k (G.nbr v r) =
        clippedOpinion G c d g Z k (G.nbr v r) := by
      intro r hr
      exact ih _ (fun i hi => hf i (inBall_neighbor_subset G v hr k hi))
        (fun t ht i hi => hW t (by omega) i (inBall_neighbor_subset G v hr k hi))
    simp only [clippedOpinion, Δ]
    rw [hc, hW k (by omega) v (root_mem_inBall G v (k+1))]
    congr 3
    apply Finset.sum_congr rfl
    intro r hr
    rw [hn r (Finset.mem_range.mp hr)]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Set MeasureTheory
open scoped Classical

noncomputable def boxInitial {V : Type*} (S : Set V) (k : ℕ) (x : SignalSlot S k → ℝ) (i : V) : ℝ :=
  if h : i ∈ S then x (none,⟨i,h⟩) else 0

noncomputable def boxSignals {V : Type*} (S : Set V) (k : ℕ) (x : SignalSlot S k → ℝ) (t : ℕ) (i : V) : ℝ :=
  if ht : t < k then if hi : i ∈ S then x (some ⟨t,ht⟩,⟨i,hi⟩) else 0 else 0

def boxValues {V : Type*} (S : Set V) (k : ℕ) (f : V → ℝ) (W : ℕ → V → ℝ) : SignalSlot S k → ℝ
  | (none,i) => f i
  | (some t,i) => W t i

theorem boxInitial_values {V : Type*} (S : Set V) (k : ℕ) (f : V → ℝ) (W : ℕ → V → ℝ)
    (i : V) (hi : i ∈ S) : boxInitial S k (boxValues S k f W) i = f i := by
  simp [boxInitial,hi,boxValues]

theorem boxSignals_values {V : Type*} (S : Set V) (k : ℕ) (f : V → ℝ) (W : ℕ → V → ℝ)
    (t : ℕ) (ht : t < k) (i : V) (hi : i ∈ S) : boxSignals S k (boxValues S k f W) t i = W t i := by
  simp [boxSignals,ht,hi,boxValues]

theorem boxInitial_measurable {V : Type*} (S : Set V) (k : ℕ) (i : V) :
    Measurable (fun x : SignalSlot S k → ℝ => boxInitial S k x i) := by
  classical
  unfold boxInitial
  split_ifs <;> fun_prop

theorem boxSignals_measurable {V : Type*} (S : Set V) (k : ℕ) (t : ℕ) (i : V) :
    Measurable (fun x : SignalSlot S k → ℝ => boxSignals S k x t i) := by
  classical
  unfold boxSignals
  split_ifs <;> fun_prop

theorem box_opinion_eq {V : Type*} (G : WDigraph V) (c d : ℝ) (v : V) (S : Set V)
    (k r : ℕ) (hr : r ≤ k) (hS : inBall G v k ⊆ S) (f : V → ℝ) (W : ℕ → V → ℝ) :
    clippedOpinion G c d (boxInitial S k (boxValues S k f W))
      (boxSignals S k (boxValues S k f W)) r v = clippedOpinion G c d f W r v := by
  apply clippedOpinion_locality
  · intro i hi
    exact boxInitial_values S k f W i (hS (inBall_mono G v hr hi))
  · intro t ht i hi
    exact boxSignals_values S k f W t (by omega) i (hS (inBall_mono G v hr hi))

theorem clippedOpinion_clip_inputs {V : Type*} (G : WDigraph V) (c d : ℝ)
    (f : V → ℝ) (W : ℕ → V → ℝ) : ∀ k,
    clippedOpinion G c d (fun i => clip (-1) 1 (f i)) (fun t i => clip (-1) 1 (W t i)) k =
      clippedOpinion G c d f W k := by
  intro k
  induction k with
  | zero => funext i; exact clip_eq (clip_mem (by norm_num) _)
  | succ k ih =>
    funext i
    simp only [clippedOpinion,ih,clip_eq (clip_mem (by norm_num : (-1:ℝ) ≤ 1) _)]

def boxNoiseEmbedding {V : Type*} (S : Set V) (k : ℕ) (p : SignalSlot S k) : Option ℕ × V :=
  (p.1.map Fin.val,p.2.val)

theorem boxNoiseEmbedding_injective {V : Type*} (S : Set V) (k : ℕ) :
    Function.Injective (boxNoiseEmbedding S k) := by
  intro p q hp
  have h1 : p.1.map Fin.val=q.1.map Fin.val := congrArg Prod.fst hp
  have h2 : p.2.val=q.2.val := congrArg Prod.snd hp
  exact Prod.ext (Option.map_injective Fin.val_injective h1) (Subtype.ext h2)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Finset

theorem clip_lipschitz_abs (lo hi x y : ℝ) : |clip lo hi x - clip lo hi y| ≤ |x-y| := by
  have h1 := abs_max_sub_max_le_max lo (min hi x) lo (min hi y)
  have h2 := abs_min_sub_min_le_max hi x hi y
  have h1a : |clip lo hi x-clip lo hi y| ≤ |min hi x-min hi y| := by
    simpa only [clip,sub_self,abs_zero,max_eq_right (abs_nonneg (min hi x-min hi y))] using h1
  have h2a : |min hi x-min hi y| ≤ |x-y| := by
    simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (x-y))] using h2
  exact h1a.trans h2a

theorem weighted_difference_bound {I : Type*} (s : Finset I) (a b x y : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hy : ∀ i ∈ s, |y i| ≤ 1) :
    |(∑ i ∈ s, a i*x i) - ∑ i ∈ s, b i*y i| ≤
      (∑ i ∈ s, a i*|x i-y i|) + ∑ i ∈ s, |a i-b i| := by
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  calc
    |a i*x i-b i*y i| = |a i*(x i-y i)+(a i-b i)*y i| := by congr 1; ring
    _ ≤ |a i*(x i-y i)| + |(a i-b i)*y i| := abs_add_le _ _
    _ ≤ a i*|x i-y i| + |a i-b i| := by
      rw [abs_mul, abs_of_nonneg (ha i hi), abs_mul]
      exact add_le_add le_rfl (by nlinarith [hy i hi, abs_nonneg (a i-b i)])

theorem clipped_step_distance_bound {I : Type*} (s : Finset I) (a b x y : I → ℝ)
    (r X Y w z : ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hr : 0 ≤ r)
    (hy : ∀ i ∈ s, |y i| ≤ 1) :
    |clip (-1) 1 ((∑ i ∈ s,a i*x i)+r*X+clip (-1) 1 w) -
      clip (-1) 1 ((∑ i ∈ s,b i*y i)+r*Y+clip (-1) 1 z)| ≤
    (∑ i ∈ s,a i*|x i-y i|) + (∑ i ∈ s,|a i-b i|) + r*|X-Y|+|w-z| := by
  apply (clip_lipschitz_abs _ _ _ _).trans
  have he : ((∑ i ∈ s,a i*x i)+r*X+clip (-1) 1 w) -
      ((∑ i ∈ s,b i*y i)+r*Y+clip (-1) 1 z) =
      ((∑ i ∈ s,a i*x i)-(∑ i ∈ s,b i*y i)) + r*(X-Y) +
        (clip (-1) 1 w-clip (-1) 1 z) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hmain := weighted_difference_bound s a b x y ha hy
  have hclip := clip_lipschitz_abs (-1) 1 w z
  have hab := abs_add_le ((∑ i ∈ s,a i*x i)-(∑ i ∈ s,b i*y i)) (r*(X-Y))
  rw [abs_mul,abs_of_nonneg hr] at hab
  linarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Finset

theorem expected_step_bound {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset I) (a b : I → ℝ) (r e η ε : ℝ)
    (F G : I → Ω → ℝ) (X Y W Z : Ω → ℝ)
    (hF : ∀ i ∈ s, Measurable (F i)) (hG : ∀ i ∈ s, Measurable (G i))
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hr : 0 ≤ r)
    (hGb : ∀ ω i, i ∈ s → |G i ω| ≤ 1)
    (hFi : ∀ i ∈ s, Integrable (fun ω => |F i ω-G i ω|) μ)
    (hXi : Integrable (fun ω => |X ω-Y ω|) μ)
    (hWi : Integrable (fun ω => |W ω-Z ω|) μ)
    (hFe : ∀ i ∈ s, (∫ ω, |F i ω-G i ω| ∂μ) ≤ e)
    (hXe : (∫ ω, |X ω-Y ω| ∂μ) ≤ e)
    (hWe : (∫ ω, |W ω-Z ω| ∂μ) ≤ η)
    (hab : (∑ i ∈ s,|a i-b i|) ≤ ε) :
    (∫ ω, |clip (-1) 1 ((∑ i ∈ s,a i*F i ω)+r*X ω+clip (-1) 1 (W ω)) -
      clip (-1) 1 ((∑ i ∈ s,b i*G i ω)+r*Y ω+clip (-1) 1 (Z ω))| ∂μ) ≤
      ((∑ i ∈ s,a i)+r)*e+ε+η := by
  let T : Ω → ℝ := fun ω =>
    |clip (-1) 1 ((∑ i ∈ s,a i*F i ω)+r*X ω+clip (-1) 1 (W ω)) -
      clip (-1) 1 ((∑ i ∈ s,b i*G i ω)+r*Y ω+clip (-1) 1 (Z ω))|
  have hTm : Measurable T := by
    unfold T
    have hsF : Measurable (fun ω => ∑ i ∈ s,a i*F i ω) := Finset.measurable_sum s (fun i hi => measurable_const.mul (hF i hi))
    have hsG : Measurable (fun ω => ∑ i ∈ s,b i*G i ω) := Finset.measurable_sum s (fun i hi => measurable_const.mul (hG i hi))
    exact (((continuous_clip (-1) 1).measurable.comp
      ((hsF.add (measurable_const.mul hX)).add ((continuous_clip (-1) 1).measurable.comp hW))).sub
      ((continuous_clip (-1) 1).measurable.comp
      ((hsG.add (measurable_const.mul hY)).add ((continuous_clip (-1) 1).measurable.comp hZ)))).abs
  have hTi : Integrable T μ := by
    apply Integrable.of_bound hTm.aestronglyMeasurable 2
    apply Filter.Eventually.of_forall
    intro ω
    have h1 := clip_mem (by norm_num : (-1:ℝ) ≤ 1) ((∑ i ∈ s,a i*F i ω)+r*X ω+clip (-1) 1 (W ω))
    have h2 := clip_mem (by norm_num : (-1:ℝ) ≤ 1) ((∑ i ∈ s,b i*G i ω)+r*Y ω+clip (-1) 1 (Z ω))
    change ‖|_-_|‖ ≤ 2
    rw [Real.norm_eq_abs,abs_abs]
    exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩
  have hsI : Integrable (fun ω => ∑ i ∈ s,a i*|F i ω-G i ω|) μ :=
    integrable_finsetSum s (fun i hi => (hFi i hi).const_mul (a i))
  have hIA : Integrable (fun ω => (∑ i ∈ s,a i*|F i ω-G i ω|) + (∑ i ∈ s,|a i-b i|)) μ :=
    hsI.add (integrable_const _)
  have hIB : Integrable (fun ω => (∑ i ∈ s,a i*|F i ω-G i ω|) + (∑ i ∈ s,|a i-b i|) + r*|X ω-Y ω|) μ :=
    hIA.add (hXi.const_mul r)
  have hI := integral_mono_ae hTi (hIB.add hWi) (Filter.Eventually.of_forall fun ω =>
      clipped_step_distance_bound s a b (fun i => F i ω) (fun i => G i ω)
        r (X ω) (Y ω) (W ω) (Z ω) ha hr (hGb ω))
  have he1 := integral_add hIB hWi
  have he2 := integral_add hIA (hXi.const_mul r)
  have he3 := integral_add hsI (integrable_const (∑ i ∈ s,|a i-b i|))
  simp only [Pi.add_apply] at hI he1 he2 he3
  rw [he1,he2,he3,integral_const,integral_const_mul,
    integral_finsetSum s (fun i hi => (hFi i hi).const_mul (a i))] at hI
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul,integral_const_mul] at hI
  have hsum : (∑ i ∈ s,a i*(∫ ω,|F i ω-G i ω| ∂μ)) ≤ (∑ i ∈ s,a i)*e := by
    rw [sum_mul]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hFe i hi) (ha i hi)
  have hself := mul_le_mul_of_nonneg_left hXe hr
  change (∫ ω,T ω ∂μ) ≤ _
  nlinarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

theorem bounded_difference_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ ω, f ω ∈ Icc (-1:ℝ) 1) (hgb : ∀ ω, g ω ∈ Icc (-1:ℝ) 1) :
    Integrable (fun ω => |f ω-g ω|) μ := by
  apply Integrable.of_bound (hf.sub hg).abs.aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_abs]
  change |f ω-g ω| ≤ 2
  exact abs_le.mpr ⟨by linarith [(hfb ω).1,(hgb ω).2],by linarith [(hfb ω).2,(hgb ω).1]⟩

theorem integral_clip_difference_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun ω => |f ω-g ω|) μ) :
    (∫ ω, |clip (-1) 1 (f ω)-clip (-1) 1 (g ω)| ∂μ) ≤ ∫ ω,|f ω-g ω| ∂μ := by
  apply integral_mono_ae
    (bounded_difference_integrable μ ((continuous_clip (-1) 1).measurable.comp hf)
      ((continuous_clip (-1) 1).measurable.comp hg)
      (fun _ => clip_mem (by norm_num) _) (fun _ => clip_mem (by norm_num) _)) hi
  exact Filter.Eventually.of_forall fun ω => clip_lipschitz_abs (-1) 1 (f ω) (g ω)

theorem fixed_clippedOpinion_measurable {Ω V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (G : WDigraph V) (c d : ℝ) (R0 : Ω → V → ℝ) (W : Ω → ℕ → V → ℝ)
    (hR : ∀ i, Measurable (fun ω => R0 ω i))
    (hW : ∀ k i, Measurable (fun ω => W ω k i)) (k : ℕ) (i : V) :
    Measurable (fun ω => clippedOpinion G c d (R0 ω) (W ω) k i) :=
  clippedOpinion_measurable (fun _ => G) c d R0 W
    (fun _ => measurable_const) (fun _ _ => measurable_const) (fun _ _ => measurable_const) hR hW k i

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

noncomputable def finiteMix {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p : I → ℝ) (μ : I → Measure X) : Measure X :=
  ∑ i, ENNReal.ofReal (p i) • μ i

theorem finite_mix_apply {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p : I → ℝ) (μ : I → Measure X) (s : Set X) :
    finiteMix p μ s = ∑ i, ENNReal.ofReal (p i) * μ i s := by
  simp [finiteMix, Measure.finsetSum_apply, Measure.smul_apply]

theorem finite_mix_map {I X Y : Type*} [Fintype I]
    [MeasurableSpace X] [MeasurableSpace Y]
    (p : I → ℝ) (μ : I → Measure X) {f : X → Y} (hf : Measurable f) :
    (finiteMix p μ).map f = finiteMix p (fun i => (μ i).map f) := by
  simp [finiteMix, ← Measure.mapₗ_apply_of_measurable hf]

theorem finite_mix_probability {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p : I → ℝ) (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    IsProbabilityMeasure (finiteMix p μ) := by
  constructor
  rw [finite_mix_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs, ENNReal.ofReal_one]

theorem finite_mix_lintegral {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p : I → ℝ) (μ : I → Measure X) (f : X → ℝ≥0∞) :
    (∫⁻ x, f x ∂finiteMix p μ) =
      ∑ i, ENNReal.ofReal (p i) * ∫⁻ x, f x ∂μ i := by
  simp [finiteMix, lintegral_finsetSum_measure, lintegral_smul_measure]

theorem coupling_finite_mix {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p : I → ℝ) (μ ν : I → Measure X) (π : I → Measure (X × X))
    (hπ : ∀ i, IsCoupling (π i) (μ i) (ν i))
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    IsCoupling (finiteMix p π) (finiteMix p μ) (finiteMix p ν) := by
  let : ∀ i, IsProbabilityMeasure (π i) := fun i => (hπ i).1
  refine ⟨finite_mix_probability p π hp hs, ?_, ?_⟩
  · rw [finite_mix_map p π measurable_fst]
    congr 1
    funext i
    exact (hπ i).2.1
  · rw [finite_mix_map p π measurable_snd]
    congr 1
    funext i
    exact (hπ i).2.2

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

def gridResidual {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ :=
  ∑ i, (p i - min (p i) (q i))

open Classical in
noncomputable def gridCouplingWeight {I : Type*} [Fintype I] (p q : I → ℝ) (i j : I) : ℝ :=
  (if i = j then min (p i) (q i) else 0) +
    (p i - min (p i) (q i)) * (q j - min (p j) (q j)) / gridResidual p q

theorem grid_residual_nonneg {I : Type*} [Fintype I] (p q : I → ℝ) :
    0 ≤ gridResidual p q := by
  exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (min_le_left (p i) (q i))

theorem grid_residual_eq {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    gridResidual p q = gridResidual q p := by
  simp only [gridResidual, Finset.sum_sub_distrib, hp, hq, min_comm]

theorem grid_deficit_le_residual {I : Type*} [Fintype I] (p q : I → ℝ) (i : I) :
    p i - min (p i) (q i) ≤ gridResidual p q := by
  exact Finset.single_le_sum
    (fun j _ => sub_nonneg.mpr (min_le_left (p j) (q j))) (Finset.mem_univ i)

theorem grid_weight_nonneg {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (i j : I) :
    0 ≤ gridCouplingWeight p q i j := by
  classical
  unfold gridCouplingWeight
  apply add_nonneg
  · split_ifs
    · exact le_min (hp i) (hq i)
    · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
        (sub_nonneg.mpr (min_le_right _ _))) (grid_residual_nonneg p q)

theorem grid_weight_row {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (i : I) :
    ∑ j, gridCouplingWeight p q i j = p i := by
  classical
  have hs : ∑ j, (q j - min (p j) (q j)) = gridResidual p q := by
    rw [grid_residual_eq p q hp hq]
    simp only [gridResidual, min_comm]
  have hsum : ∑ j, gridCouplingWeight p q i j = min (p i) (q i) +
      (p i - min (p i) (q i)) * gridResidual p q / gridResidual p q := by
    simp only [gridCouplingWeight, Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.mul_sum]
    simp [hs]
  rw [hsum]
  by_cases hR : gridResidual p q = 0
  · have he : p i - min (p i) (q i) = 0 := by
      have hle := grid_deficit_le_residual p q i
      have hge := min_le_left (p i) (q i)
      rw [hR] at hle
      linarith
    rw [hR, mul_zero, zero_div, add_zero]
    exact (sub_eq_zero.mp he).symm
  · rw [mul_div_cancel_right₀ _ hR]
    ring

theorem grid_weight_transpose {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (i j : I) :
    gridCouplingWeight p q i j = gridCouplingWeight q p j i := by
  classical
  simp only [gridCouplingWeight, grid_residual_eq p q hp hq, min_comm]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    ring
  · simp only [hij, Ne.symm hij, ite_false]
    ring

theorem grid_weight_col {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) (j : I) :
    ∑ i, gridCouplingWeight p q i j = q j := by
  simp_rw [grid_weight_transpose p q hp hq]
  exact grid_weight_row q p hq hp j

theorem grid_residual_le_abs {I : Type*} [Fintype I] (p q : I → ℝ) :
    gridResidual p q ≤ ∑ i, |p i - q i| := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : p i ≤ q i
  · simp only [min_eq_left h, sub_self]
    exact abs_nonneg _
  · have h' : q i ≤ p i := le_of_not_ge h
    rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h')]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem finite_mix_matrix_left {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j) (μ : I → Measure X) :
    finiteMix (fun z : I × J => w z.1 z.2) (fun z => μ z.1) =
      finiteMix (fun i => ∑ j, w i j) μ := by
  unfold finiteMix
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hw i j), Finset.sum_smul]

theorem finite_mix_matrix_right {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j) (ν : J → Measure X) :
    finiteMix (fun z : I × J => w z.1 z.2) (fun z => ν z.2) =
      finiteMix (fun j => ∑ i, w i j) ν := by
  unfold finiteMix
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i j), Finset.sum_smul]

theorem matrix_measure_coupling {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (p : I → ℝ) (q : J → ℝ) (μ : I → Measure X) (ν : J → Measure X)
    (w : I → J → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = p i) (hcol : ∀ j, ∑ i, w i j = q j)
    (hp : ∑ i, p i = 1) (π : I → J → Measure (X × X))
    (hπ : ∀ i j, IsCoupling (π i j) (μ i) (ν j)) :
    IsCoupling (finiteMix (fun z : I × J => w z.1 z.2) (fun z => π z.1 z.2))
      (finiteMix p μ) (finiteMix q ν) := by
  have hs : ∑ z : I × J, w z.1 z.2 = 1 := by
    simp only [Fintype.sum_prod_type, hrow, hp]
  have h := coupling_finite_mix (fun z : I × J => w z.1 z.2)
    (fun z => μ z.1) (fun z => ν z.2) (fun z => π z.1 z.2)
    (fun z => hπ z.1 z.2) (fun z => hw z.1 z.2) hs
  rw [finite_mix_matrix_left w hw μ, finite_mix_matrix_right w hw ν] at h
  simpa only [hrow, hcol] using h

theorem grid_measure_coupling {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p q : I → ℝ) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    IsCoupling
      (finiteMix (fun z : I × I => gridCouplingWeight p q z.1 z.2)
        (fun z => (μ z.1).prod (ν z.2))) (finiteMix p μ) (finiteMix q ν) := by
  exact matrix_measure_coupling p q μ ν (gridCouplingWeight p q)
    (grid_weight_nonneg p q hp hq) (grid_weight_row p q hps hqs)
    (grid_weight_col p q hps hqs) hps (fun i j => (μ i).prod (ν j))
    (fun i j => coupling_prod (μ i) (ν j))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open Finset

theorem grid_residual_pair_sum {I : Type*} [Fintype I] (p q : I → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1) :
    (∑ i, ∑ j, (p i - min (p i) (q i)) * (q j - min (p j) (q j)) /
      gridResidual p q) = gridResidual p q := by
  have hs : ∑ j, (q j - min (p j) (q j)) = gridResidual p q := by
    rw [grid_residual_eq p q hp hq]
    simp only [gridResidual, min_comm]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [hs, ← Finset.sum_mul]
  change gridResidual p q * gridResidual p q / gridResidual p q = gridResidual p q
  by_cases hR : gridResidual p q = 0
  · simp [hR]
  · exact mul_div_cancel_right₀ _ hR

theorem grid_weighted_cost_bound {I : Type*} [Fintype I]
    (p q : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (cost : I → I → ℝ) (ε D : ℝ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, cost i i ≤ ε) (hD : ∀ i j, cost i j ≤ D) :
    (∑ i, ∑ j, gridCouplingWeight p q i j * cost i j) ≤
      ε + D * gridResidual p q := by
  classical
  let a : I → I → ℝ := fun i j =>
    (p i - min (p i) (q i)) * (q j - min (p j) (q j)) / gridResidual p q
  have ha : ∀ i j, 0 ≤ a i j := fun i j =>
    div_nonneg (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
      (sub_nonneg.mpr (min_le_right _ _))) (grid_residual_nonneg p q)
  have has : ∑ i, ∑ j, a i j = gridResidual p q :=
    grid_residual_pair_sum p q hps hqs
  have hsplit : (∑ i, ∑ j, gridCouplingWeight p q i j * cost i j) =
      (∑ i, min (p i) (q i) * cost i i) + ∑ i, ∑ j, a i j * cost i j := by
    simp only [gridCouplingWeight, add_mul, Finset.sum_add_distrib]
    simp [a]
  have hclose : (∑ i, min (p i) (q i) * cost i i) ≤
      (∑ i, min (p i) (q i)) * ε := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hdiag i) (le_min (hp i) (hq i))
  have hfar : (∑ i, ∑ j, a i j * cost i j) ≤ gridResidual p q * D := by
    rw [← has, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hD i j) (ha i j)
  have hmass : (∑ i, min (p i) (q i)) ≤ 1 := by
    rw [← hps]
    exact Finset.sum_le_sum fun i _ => min_le_left _ _
  rw [hsplit]
  exact (add_le_add hclose hfar).trans (by nlinarith [mul_le_mul_of_nonneg_right hmass hε])

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem grid_transport_integral_bound {I X : Type*} [Fintype I] [MeasurableSpace X]
    (p q : I → ℝ) (μ ν : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (g : X × X → ℝ) (hg : ∀ z, 0 ≤ g z)
    (hi : ∀ i j, Integrable g ((μ i).prod (ν j)))
    (ε D : ℝ) (hε : 0 ≤ ε)
    (hdiag : ∀ i, (∫ z, g z ∂((μ i).prod (ν i))) ≤ ε)
    (hD : ∀ i j, (∫ z, g z ∂((μ i).prod (ν j))) ≤ D) :
    RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (g (x,y)))
      (finiteMix p μ) (finiteMix q ν) ≤ ENNReal.ofReal (ε + D * gridResidual p q) := by
  let cost : I → I → ℝ := fun i j => ∫ z, g z ∂((μ i).prod (ν j))
  have hc : ∀ i j, 0 ≤ cost i j := fun _ _ => integral_nonneg hg
  have hw := grid_weight_nonneg p q hp hq
  have hterm : ∀ z : I × I,
      ENNReal.ofReal (gridCouplingWeight p q z.1 z.2) *
        (∫⁻ x, ENNReal.ofReal (g x) ∂((μ z.1).prod (ν z.2))) =
      ENNReal.ofReal (gridCouplingWeight p q z.1 z.2 * cost z.1 z.2) := by
    intro z
    rw [← ofReal_integral_eq_lintegral_ofReal (hi z.1 z.2)
      (Filter.Eventually.of_forall hg), ← ENNReal.ofReal_mul (hw z.1 z.2)]
  calc
    RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (g (x,y)))
        (finiteMix p μ) (finiteMix q ν) ≤
        ∫⁻ z, ENNReal.ofReal (g z) ∂finiteMix
          (fun z : I × I => gridCouplingWeight p q z.1 z.2)
          (fun z => (μ z.1).prod (ν z.2)) :=
      transport_le_coupling _ (grid_measure_coupling p q μ ν hp hq hps hqs)
    _ = ∑ z : I × I, ENNReal.ofReal (gridCouplingWeight p q z.1 z.2 * cost z.1 z.2) := by
      rw [finite_mix_lintegral]
      exact Finset.sum_congr rfl (fun z _ => hterm z)
    _ = ENNReal.ofReal (∑ z : I × I, gridCouplingWeight p q z.1 z.2 * cost z.1 z.2) :=
      (ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (hw z.1 z.2) (hc z.1 z.2))).symm
    _ ≤ ENNReal.ofReal (ε + D * gridResidual p q) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Fintype.sum_prod_type]
      exact grid_weighted_cost_bound p q hp hq hps hqs cost ε D hε hdiag hD

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

noncomputable def normalizeOrDirac {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (x : X) : Measure X :=
  if ν univ = 0 then Measure.dirac x else (ν univ)⁻¹ • ν

theorem normalize_or_dirac_probability {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (x : X) :
    IsProbabilityMeasure (normalizeOrDirac ν x) := by
  classical
  unfold normalizeOrDirac
  split_ifs with h
  · infer_instance
  · constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h (measure_ne_top ν univ)

theorem normalize_or_dirac_reconstruct {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (x : X) :
    ν univ • normalizeOrDirac ν x = ν := by
  classical
  unfold normalizeOrDirac
  split_ifs with h
  · have hz : ν = 0 := Measure.measure_univ_eq_zero.mp h
    simp [hz]
  · rw [smul_smul, ENNReal.mul_inv_cancel h (measure_ne_top ν univ), one_smul]

theorem normalize_or_dirac_ae {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) (x : X) {p : X → Prop}
    (hν : ∀ᵐ y ∂ν, p y) (hx : p x) :
    ∀ᵐ y ∂normalizeOrDirac ν x, p y := by
  classical
  unfold normalizeOrDirac
  split_ifs
  · simpa using hx
  · exact Measure.ae_smul_measure hν _

theorem density_mass_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x))) univ = ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hn)).symm

theorem density_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [density_mass_integral μ hf hn]
  exact ENNReal.ofReal_lt_top

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

noncomputable def partitionMass {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (i : I) : ℝ := ∫ x, φ i x ∂μ

noncomputable def partitionPiece {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (z : I → X) (i : I) : Measure X :=
  normalizeOrDirac (μ.withDensity (fun x => ENNReal.ofReal (φ i x))) (z i)

theorem partition_mass_nonneg {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (hφ : ∀ i x, 0 ≤ φ i x) (i : I) :
    0 ≤ partitionMass μ φ i := integral_nonneg (hφ i)

theorem partition_mass_sum {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (φ : I → X → ℝ)
    (hi : ∀ i, Integrable (φ i) μ) (hs : ∀ x, ∑ i, φ i x = 1) :
    ∑ i, partitionMass μ φ i = 1 := by
  unfold partitionMass
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp [hs]

theorem partition_piece_probability {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (z : I → X)
    (hi : ∀ i, Integrable (φ i) μ) (hn : ∀ i x, 0 ≤ φ i x) (i : I) :
    IsProbabilityMeasure (partitionPiece μ φ z i) := by
  let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (φ i x))) :=
    density_finite μ (hi i) (hn i)
  exact normalize_or_dirac_probability _ _

theorem partition_density_sum {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (hm : ∀ i, Measurable (φ i))
    (hn : ∀ i x, 0 ≤ φ i x) (hs : ∀ x, ∑ i, φ i x = 1) :
    (∑ i, μ.withDensity (fun x => ENNReal.ofReal (φ i x))) = μ := by
  have hsum : ∀ x, ∑ i, ENNReal.ofReal (φ i x) = 1 := by
    intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hn i x), hs x, ENNReal.ofReal_one]
  ext s hsm
  rw [Measure.finsetSum_apply]
  simp_rw [withDensity_apply _ hsm]
  rw [← lintegral_finsetSum Finset.univ (fun i _ => (hm i).ennreal_ofReal)]
  simp [hsum]

theorem partition_mix_eq {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : Measure X) (φ : I → X → ℝ) (z : I → X)
    (hm : ∀ i, Measurable (φ i)) (hi : ∀ i, Integrable (φ i) μ)
    (hn : ∀ i x, 0 ≤ φ i x) (hs : ∀ x, ∑ i, φ i x = 1) :
    finiteMix (partitionMass μ φ) (partitionPiece μ φ z) = μ := by
  have hterm : ∀ i, ENNReal.ofReal (partitionMass μ φ i) • partitionPiece μ φ z i =
      μ.withDensity (fun x => ENNReal.ofReal (φ i x)) := by
    intro i
    let : IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (φ i x))) :=
      density_finite μ (hi i) (hn i)
    unfold partitionMass partitionPiece
    rw [← density_mass_integral μ (hi i) (hn i)]
    exact normalize_or_dirac_reconstruct _ _
  unfold finiteMix
  simp_rw [hterm]
  exact partition_density_sum μ φ hm hn hs

theorem partition_piece_ae {I X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) (φ : I → X → ℝ) (z : I → X) (hm : ∀ i, Measurable (φ i))
    (p : I → X → Prop) (hz : ∀ i, p i (z i))
    (hsupport : ∀ i x, φ i x ≠ 0 → p i x) (i : I) :
    ∀ᵐ x ∂partitionPiece μ φ z i, p i x := by
  apply normalize_or_dirac_ae _ _ _ (hz i)
  rw [ae_withDensity_iff (hm i).ennreal_ofReal]
  exact Filter.Eventually.of_forall fun x h => hsupport i x fun he => h (by simp [he])

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem compact_grid_partition {X : Type*} [MetricSpace X] [CompactSpace X]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset X, ∃ φ : s → C(X, ℝ),
      (∀ i x, 0 ≤ φ i x) ∧ (∀ x, ∑ i, φ i x = 1) ∧
      (∀ i x, φ i x ≠ 0 → dist x (i : X) ≤ δ) := by
  classical
  have hcover : (univ : Set X) ⊆ ⋃ x : X, Metric.ball x δ := by
    intro x _
    exact mem_iUnion.mpr ⟨x, by simpa using hδ⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => Metric.ball x δ) (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (univ : Set X) ⊆ ⋃ i : s, Metric.ball (i : X) δ := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i, his⟩, hxi⟩
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : s => Metric.ball (i : X) δ) (fun _ => Metric.isOpen_ball) hcover'
  refine ⟨s, (fun i => φ i), φ.nonneg, ?_, ?_⟩
  · intro x
    simpa only [finsum_eq_sum_of_fintype] using φ.sum_eq_one (mem_univ x)
  · intro i x hx
    exact (hφ i (subset_tsupport (φ i) hx)).le

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem compact_partition_transport_bound {I X : Type*} [Fintype I]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (φ : I → C(X, ℝ)) (z : I → X) (δ D : ℝ) (hδ : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hn : ∀ i x, 0 ≤ φ i x) (hs : ∀ x, ∑ i, φ i x = 1)
    (hnear : ∀ i x, φ i x ≠ 0 → dist x (z i) ≤ δ)
    (hdiam : ∀ x y : X, dist x y ≤ D) :
    RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y)) μ ν ≤
      ENNReal.ofReal (2 * δ + D * ∑ i, |(∫ x, φ i x ∂μ) - ∫ x, φ i x ∂ν|) := by
  let f : I → X → ℝ := fun i => φ i
  have hm : ∀ i, Measurable (f i) := fun i => (φ i).continuous.measurable
  have hiμ : ∀ i, Integrable (f i) μ := fun i =>
    (φ i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiν : ∀ i, Integrable (f i) ν := fun i =>
    (φ i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ξ := partitionPiece μ f z
  let η := partitionPiece ν f z
  let p := partitionMass μ f
  let q := partitionMass ν f
  let : ∀ i, IsProbabilityMeasure (ξ i) := partition_piece_probability μ f z hiμ hn
  let : ∀ i, IsProbabilityMeasure (η i) := partition_piece_probability ν f z hiν hn
  have hcost : ∀ i j, Integrable (fun a : X × X => dist a.1 a.2) ((ξ i).prod (η j)) :=
    fun _ _ => continuous_dist.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdiag : ∀ i, (∫ a : X × X, dist a.1 a.2 ∂((ξ i).prod (η i))) ≤ 2 * δ := by
    intro i
    have hx : ∀ᵐ x ∂ξ i, dist x (z i) ≤ δ := partition_piece_ae μ f z hm
      (fun j x => dist x (z j) ≤ δ) (fun _ => by simpa using hδ) hnear i
    have hy : ∀ᵐ y ∂η i, dist y (z i) ≤ δ := partition_piece_ae ν f z hm
      (fun j y => dist y (z j) ≤ δ) (fun _ => by simpa using hδ) hnear i
    have hxy : ∀ᵐ a ∂(ξ i).prod (η i), dist a.1 a.2 ≤ 2 * δ := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_le continuous_dist.measurable measurable_const)).2
      filter_upwards [hx] with x hxx
      filter_upwards [hy] with y hyy
      have ht := dist_triangle x (z i) y
      rw [dist_comm (z i) y] at ht
      linarith
    calc
      (∫ a : X × X, dist a.1 a.2 ∂((ξ i).prod (η i))) ≤
          ∫ _ : X × X, 2 * δ ∂((ξ i).prod (η i)) :=
        integral_mono_ae (hcost i i) (integrable_const _) hxy
      _ = 2 * δ := by simp
  have hall : ∀ i j, (∫ a : X × X, dist a.1 a.2 ∂((ξ i).prod (η j))) ≤ D := by
    intro i j
    calc
      (∫ a : X × X, dist a.1 a.2 ∂((ξ i).prod (η j))) ≤
          ∫ _ : X × X, D ∂((ξ i).prod (η j)) :=
        integral_mono (hcost i j) (integrable_const _) (fun a => hdiam a.1 a.2)
      _ = D := by simp
  have hb := grid_transport_integral_bound p q ξ η
    (partition_mass_nonneg μ f hn) (partition_mass_nonneg ν f hn)
    (partition_mass_sum μ f hiμ hs) (partition_mass_sum ν f hiν hs)
    (fun a : X × X => dist a.1 a.2) (fun _ => dist_nonneg) hcost
    (2 * δ) D (by positivity) hdiag hall
  have hμeq : finiteMix p ξ = μ := partition_mix_eq μ f z hm hiμ hn hs
  have hνeq : finiteMix q η = ν := partition_mix_eq ν f z hm hiν hn hs
  rw [hμeq, hνeq] at hb
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (grid_residual_le_abs p q) hD0)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem compact_transport_in_probability {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) (μ : ℕ → Ω → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (hμ : ∀ f : C(X, ℝ), TendstoInMeasure P
      (fun n ω => ∫ x, f x ∂(μ n ω : Measure X)) atTop
      (fun _ => ∫ x, f x ∂(ν : Measure X)))
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y : X, dist x y ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤
      RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y))
        (μ n ω : Measure X) (ν : Measure X)}) atTop (𝓝 0) := by
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, φ, hn, hs, hnear⟩ := compact_grid_partition (X := X) δ hδ
  let t : ℝ := ε / (2 * (D + 1))
  have ht : 0 < t := div_pos hε (by positivity)
  have htid : 2 * (D + 1) * t = ε := by
    have hD1 : D + 1 ≠ 0 := by linarith
    dsimp [t]
    field_simp
  let err : ℕ → Ω → ℝ := fun n ω => ∑ i : s,
    |(∫ x, φ i x ∂(μ n ω : Measure X)) - ∫ x, φ i x ∂(ν : Measure X)|
  have herr : Tendsto (fun n => P {ω | t ≤ err n ω}) atTop (𝓝 0) :=
    finite_test_abs_sum_probability P
      (fun i n ω => ∫ x, φ i x ∂(μ n ω : Measure X))
      (fun i => ∫ x, φ i x ∂(ν : Measure X)) (fun i => hμ (φ i)) t ht
  have hsub : ∀ n, {ω | ENNReal.ofReal ε ≤
      RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y))
        (μ n ω : Measure X) (ν : Measure X)} ⊆ {ω | t ≤ err n ω} := by
    intro n ω hω
    by_contra hnot
    have he : err n ω < t := lt_of_not_ge hnot
    have hsmall : 2 * δ + D * err n ω < ε := by
      have hm := mul_le_mul_of_nonneg_left he.le hD
      dsimp [δ]
      nlinarith
    have hb := compact_partition_transport_bound (μ n ω : Measure X) (ν : Measure X)
      φ (fun i : s => (i : X)) δ D hδ.le hD hn hs hnear hdiam
    have hlt : RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y))
        (μ n ω : Measure X) (ν : Measure X) < ENNReal.ofReal ε :=
      hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hsmall)
    exact (not_lt_of_ge hω) hlt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
    (fun _ => bot_le) (fun n => measure_mono (hsub n))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem map_retraction_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Y) (r : Y → X) (e : X → Y) (hr : Measurable r) (he : Measurable e)
    (hfix : ∀ᵐ y ∂μ, e (r y) = y) : (μ.map r).map e = μ := by
  rw [Measure.map_map he hr]
  have h : e ∘ r =ᵐ[μ] id := hfix
  rw [Measure.map_congr h, Measure.map_id]

theorem transport_retraction_le {X Y : Type*} [MetricSpace X] [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ ν : Measure Y) (r : Y → X) (e : X → Y) (hr : Measurable r) (he : Measurable e)
    (hcost : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hμ : ∀ᵐ y ∂μ, e (r y) = y) (hν : ∀ᵐ y ∂ν, e (r y) = y) :
    RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y)) μ ν ≤
      RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y)) (μ.map r) (ν.map r) := by
  have h := transport_map_le (fun x y : X => ENNReal.ofReal (dist x y))
    (fun x y : Y => ENNReal.ofReal (dist x y)) (by exact ENNReal.measurable_ofReal.comp (measurable_fst.dist measurable_snd)) (μ.map r) (ν.map r)
    he he (fun x y => ENNReal.ofReal_le_ofReal (hcost x y))
  rw [map_retraction_eq μ r e hr he hμ, map_retraction_eq ν r e hr he hν] at h
  exact h

theorem compact_retraction_transport_in_probability {Ω X Y : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompactSpace X] [MetricSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (P : Measure Ω) (μ : ℕ → Ω → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (r : Y → X) (e : X → Y) (hr : Continuous r) (he : Continuous e)
    (hcost : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hμfix : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ y ∂(μ n ω : Measure Y), e (r y) = y)
    (hνfix : ∀ᵐ y ∂(ν : Measure Y), e (r y) = y)
    (htest : ∀ f : C(X, ℝ), TendstoInMeasure P
      (fun n ω => ∫ y, f (r y) ∂(μ n ω : Measure Y)) atTop
      (fun _ => ∫ y, f (r y) ∂(ν : Measure Y)))
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y : X, dist x y ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤
      RWPI.SqrtLasso.transportCost (fun x y => ENNReal.ofReal (dist x y))
        (μ n ω : Measure Y) (ν : Measure Y)}) atTop (𝓝 0) := by
  let μ' : ℕ → Ω → ProbabilityMeasure X := fun n ω => (μ n ω).map hr.measurable.aemeasurable
  let ν' : ProbabilityMeasure X := ν.map hr.measurable.aemeasurable
  have htest' : ∀ f : C(X, ℝ), TendstoInMeasure P
      (fun n ω => ∫ x, f x ∂(μ' n ω : Measure X)) atTop
      (fun _ => ∫ x, f x ∂(ν' : Measure X)) := by
    intro f
    have hInt : ∀ ξ : ProbabilityMeasure Y,
        (∫ x, f x ∂((ξ.map hr.measurable.aemeasurable) : Measure X)) =
          ∫ y, f (r y) ∂(ξ : Measure Y) := fun ξ =>
      integral_map hr.measurable.aemeasurable f.continuous.aestronglyMeasurable
    simpa only [μ', ν', hInt] using htest f
  have hlim := compact_transport_in_probability P μ' ν' htest' D hD hdiam ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hμfix n] with ω hω
  intro hεω
  exact hεω.trans (transport_retraction_le (μ n ω : Measure Y) (ν : Measure Y) r e
    hr.measurable he.measurable hcost hω hνfix)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

abbrev FiniteCube (k : ℕ) := Fin (k + 1) → Icc (-1 : ℝ) 1

def cubeInclusion (k : ℕ) (x : FiniteCube k) : Fin (k + 1) → ℝ := fun i => x i

def cubeRetraction (k : ℕ) (x : Fin (k + 1) → ℝ) : FiniteCube k :=
  fun i => ⟨clip (-1) 1 (x i), clip_mem (by norm_num) _⟩

theorem cubeInclusion_isometry (k : ℕ) : Isometry (cubeInclusion k) :=
  Isometry.piMap (fun _ : Fin (k + 1) => ((↑) : Icc (-1 : ℝ) 1 → ℝ))
    (fun _ => isometry_subtype_coe)

theorem cubeRetraction_continuous (k : ℕ) : Continuous (cubeRetraction k) := by
  apply continuous_pi
  intro i
  exact ((continuous_clip (-1) 1).comp (continuous_apply i)).subtype_mk _

theorem cube_retraction_eq (k : ℕ) (x : Fin (k + 1) → ℝ)
    (hx : ∀ i, x i ∈ Icc (-1 : ℝ) 1) : cubeInclusion k (cubeRetraction k x) = x := by
  funext i
  exact clip_eq (hx i)

theorem cube_diameter (k : ℕ) (x y : FiniteCube k) : dist x y ≤ 2 := by
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 2)).2
  intro i
  change |(x i : ℝ) - (y i : ℝ)| ≤ 2
  rcases (x i).property with ⟨hx1, hx2⟩
  rcases (y i).property with ⟨hy1, hy2⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem finite_cube_transport_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : ℕ)
    (μ : ℕ → Ω → ProbabilityMeasure (Fin (k + 1) → ℝ))
    (ν : ProbabilityMeasure (Fin (k + 1) → ℝ))
    (hμ : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ n ω : Measure (Fin (k + 1) → ℝ)),
      ∀ i, x i ∈ Icc (-1 : ℝ) 1)
    (hν : ∀ᵐ x ∂(ν : Measure (Fin (k + 1) → ℝ)), ∀ i, x i ∈ Icc (-1 : ℝ) 1)
    (htest : ∀ f : C(FiniteCube k, ℝ), TendstoInMeasure P
      (fun n ω => ∫ x, f (cubeRetraction k x) ∂(μ n ω : Measure (Fin (k + 1) → ℝ)))
      atTop (fun _ => ∫ x, f (cubeRetraction k x) ∂(ν : Measure (Fin (k + 1) → ℝ))))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤ W1vec
      (μ n ω : Measure (Fin (k + 1) → ℝ)) (ν : Measure (Fin (k + 1) → ℝ))})
      atTop (𝓝 0) := by
  have hfixμ : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ n ω : Measure (Fin (k + 1) → ℝ)),
      cubeInclusion k (cubeRetraction k x) = x := by
    intro n
    filter_upwards [hμ n] with ω hω
    filter_upwards [hω] with x hx
    exact cube_retraction_eq k x hx
  have hfixν : ∀ᵐ x ∂(ν : Measure (Fin (k + 1) → ℝ)),
      cubeInclusion k (cubeRetraction k x) = x := by
    filter_upwards [hν] with x hx
    exact cube_retraction_eq k x hx
  simpa only [W1vec, edist_dist] using
    compact_retraction_transport_in_probability P μ ν (cubeRetraction k) (cubeInclusion k)
      (cubeRetraction_continuous k) (cubeInclusion_isometry k).continuous
      (fun x y => (cubeInclusion_isometry k).dist_eq x y |>.le) hfixμ hfixν htest
      2 (by norm_num) (cube_diameter k) ε hε

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Finset Set

noncomputable def boxTrajectory {V : Type*} (G : WDigraph V) (v : V) (S : Set V)
    (c d : ℝ) (k : ℕ) (x : SignalSlot S k → ℝ) : Fin (k+1) → ℝ :=
  fun r => clippedOpinion G c d (boxInitial S k x) (boxSignals S k x) r v

theorem boxTrajectory_measurable {V : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (G : WDigraph V) (v : V) (S : Set V) (c d : ℝ) (k : ℕ) :
    Measurable (boxTrajectory G v S c d k) := by
  apply measurable_pi_lambda
  intro r
  exact fixed_clippedOpinion_measurable G c d (boxInitial S k) (boxSignals S k)
    (boxInitial_measurable S k) (boxSignals_measurable S k) r v

theorem boxTrajectory_mem {V : Type*} (G : WDigraph V) (v : V) (S : Set V) (c d : ℝ)
    (k : ℕ) (x : SignalSlot S k → ℝ) (r : Fin (k+1)) : boxTrajectory G v S c d k x r ∈ Icc (-1:ℝ) 1 :=
  clippedOpinion_mem _ _ _ _ _ _ _

theorem cube_distance_le_sum (k : ℕ) (x y : Fin (k+1) → ℝ) :
    dist (cubeRetraction k x) (cubeRetraction k y) ≤ ∑ r,|x r-y r| := by
  apply (dist_pi_le_iff (sum_nonneg fun _ _ => abs_nonneg _)).mpr
  intro r
  change |clip (-1) 1 (x r)-clip (-1) 1 (y r)| ≤ _
  apply (clip_lipschitz_abs (-1) 1 _ _).trans
  exact single_le_sum (fun i _ => abs_nonneg (x i-y i)) (mem_univ r)

theorem expected_cube_distance_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (k : ℕ) (F G : Ω → Fin (k+1) → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ ω r,F ω r ∈ Icc (-1:ℝ) 1) (hGb : ∀ ω r,G ω r ∈ Icc (-1:ℝ) 1)
    (E : Fin (k+1) → ℝ) (hE : ∀ r,(∫ ω,|F ω r-G ω r| ∂μ) ≤ E r) :
    (∫ ω,dist (cubeRetraction k (F ω)) (cubeRetraction k (G ω)) ∂μ) ≤ ∑ r,E r := by
  have hFi : ∀ r,Integrable (fun ω => |F ω r-G ω r|) μ := fun r =>
    bounded_difference_integrable μ hF.eval hG.eval (fun ω => hFb ω r) (fun ω => hGb ω r)
  have hDi : Integrable (fun ω => dist (cubeRetraction k (F ω)) (cubeRetraction k (G ω))) μ := by
    apply Integrable.of_bound (((cubeRetraction_continuous k).measurable.comp hF).dist
      ((cubeRetraction_continuous k).measurable.comp hG)).aestronglyMeasurable 2
    exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,Function.comp_def] using cube_diameter k (cubeRetraction k (F ω)) (cubeRetraction k (G ω))
  have hh := integral_mono_ae hDi (integrable_finsetSum univ (fun r _ => hFi r))
    (Filter.Eventually.of_forall fun ω => cube_distance_le_sum k (F ω) (G ω))
  rw [integral_finsetSum univ (fun r _ => hFi r)] at hh
  exact hh.trans (sum_le_sum fun r _ => hE r)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

noncomputable def pairedBoxLeft {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) : SignalSlot T k → ℝ :=
  fun p => (u (p.1,θ.symm p.2)).1

noncomputable def pairedBoxRight {V : Type*} (S : Set V) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) : SignalSlot S k → ℝ := fun p => (u p).2

theorem pairedBoxLeft_measurable {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ) :
    Measurable (pairedBoxLeft θ k) := by
  unfold pairedBoxLeft
  fun_prop

theorem pairedBoxRight_measurable {V : Type*} (S : Set V) (k : ℕ) :
    Measurable (pairedBoxRight S k) := by
  unfold pairedBoxRight
  fun_prop

theorem paired_initial_left {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) (i : S) :
    boxInitial T k (pairedBoxLeft θ k u) (θ i) = (u (none,i)).1 := by
  simp [boxInitial,pairedBoxLeft,(θ i).property]

theorem paired_initial_right {V : Type*} (S : Set V) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) (i : S) :
    boxInitial S k (pairedBoxRight S k u) i = (u (none,i)).2 := by
  simp [boxInitial,pairedBoxRight,i.property]

theorem paired_signal_left {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) (t : ℕ) (ht : t<k) (i : S) :
    boxSignals T k (pairedBoxLeft θ k u) t (θ i) = (u (some ⟨t,ht⟩,i)).1 := by
  simp [boxSignals,pairedBoxLeft,ht,(θ i).property]

theorem paired_signal_right {V : Type*} (S : Set V) (k : ℕ)
    (u : SignalSlot S k → ℝ × ℝ) (t : ℕ) (ht : t<k) (i : S) :
    boxSignals S k (pairedBoxRight S k u) t i = (u (some ⟨t,ht⟩,i)).2 := by
  simp [boxSignals,pairedBoxRight,ht,i.property]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory

theorem product_coordinate_cost {I : Type*} [Fintype I]
    (π : I → Measure (ℝ × ℝ)) [∀ i,IsProbabilityMeasure (π i)] {η : ℝ}
    (hi : ∀ i,Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (π i))
    (hb : ∀ i,(∫ z,|z.1-z.2| ∂π i) ≤ η) (i : I) :
    Integrable (fun u : I → ℝ × ℝ => |(u i).1-(u i).2|) (Measure.pi π) ∧
      (∫ u : I → ℝ × ℝ, |(u i).1-(u i).2| ∂Measure.pi π) ≤ η := by
  refine ⟨(measurePreserving_eval π i).integrable_comp_of_integrable (hi i),?_⟩
  rw [product_coordinate_integral π i (fun z : ℝ × ℝ => |z.1-z.2|) (by fun_prop)]
  exact hb i

theorem paired_initial_cost {V U : Type*} {S : Set V} {T : Set U} [Fintype S]
    (θ : S ≃ T) (k : ℕ) (π : SignalSlot S k → Measure (ℝ × ℝ))
    [∀ p,IsProbabilityMeasure (π p)] {η : ℝ}
    (hi : ∀ p,Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (π p))
    (hb : ∀ p,(∫ z,|z.1-z.2| ∂π p) ≤ η) (i : S) :
    Integrable (fun u => |boxInitial T k (pairedBoxLeft θ k u) (θ i) -
      boxInitial S k (pairedBoxRight S k u) i|) (Measure.pi π) ∧
    (∫ u,|boxInitial T k (pairedBoxLeft θ k u) (θ i) -
      boxInitial S k (pairedBoxRight S k u) i| ∂Measure.pi π) ≤ η := by
  simpa only [paired_initial_left,paired_initial_right] using product_coordinate_cost π hi hb (none,i)

theorem paired_signal_cost {V U : Type*} {S : Set V} {T : Set U} [Fintype S]
    (θ : S ≃ T) (k : ℕ) (π : SignalSlot S k → Measure (ℝ × ℝ))
    [∀ p,IsProbabilityMeasure (π p)] {η : ℝ}
    (hi : ∀ p,Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (π p))
    (hb : ∀ p,(∫ z,|z.1-z.2| ∂π p) ≤ η) (t : ℕ) (ht : t<k) (i : S) :
    Integrable (fun u => |boxSignals T k (pairedBoxLeft θ k u) t (θ i) -
      boxSignals S k (pairedBoxRight S k u) t i|) (Measure.pi π) ∧
    (∫ u,|boxSignals T k (pairedBoxLeft θ k u) t (θ i) -
      boxSignals S k (pairedBoxRight S k u) t i| ∂Measure.pi π) ≤ η := by
  simpa only [paired_signal_left θ k _ t ht,paired_signal_right S k _ t ht] using
    product_coordinate_cost π hi hb (some ⟨t,ht⟩,i)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Finset

theorem local_expected_comparison {Ω V U : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : WDigraph V) (H : WDigraph U)
    (c d ε η : ℝ) (hG : G.Valid c) (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d ≤ 1)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (f : Ω → V → ℝ) (g : Ω → U → ℝ) (W : Ω → ℕ → V → ℝ) (Z : Ω → ℕ → U → ℝ)
    (hf : ∀ i, Measurable (fun ω => f ω i)) (hg : ∀ j, Measurable (fun ω => g ω j))
    (hW : ∀ t i, Measurable (fun ω => W ω t i)) (hZ : ∀ t j, Measurable (fun ω => Z ω t j))
    (R : ℕ → V → U → Prop)
    (hstay : ∀ n i j, R (n+1) i j → R n i j)
    (hdeg : ∀ n i j, R (n+1) i j → G.deg i = H.deg j)
    (hnbr : ∀ n i j, R (n+1) i j → ∀ r < G.deg i, R n (G.nbr i r) (H.nbr j r))
    (hwt : ∀ n i j, R (n+1) i j → (∑ r ∈ range (G.deg i),|G.wt i r-H.wt j r|) ≤ ε)
    (hinit : ∀ i j, R 0 i j → Integrable (fun ω => |f ω i-g ω j|) μ ∧
      (∫ ω,|f ω i-g ω j| ∂μ) ≤ η)
    (hsig : ∀ n i j, R (n+1) i j → Integrable (fun ω => |W ω n i-Z ω n j|) μ ∧
      (∫ ω,|W ω n i-Z ω n j| ∂μ) ≤ η) :
    ∀ n i j, R n i j →
      (∫ ω, |clippedOpinion G c d (f ω) (W ω) n i -
        clippedOpinion H c d (g ω) (Z ω) n j| ∂μ) ≤ ((n:ℝ)+1)*η+(n:ℝ)*ε := by
  have hFm := fixed_clippedOpinion_measurable G c d f W hf hW
  have hGm := fixed_clippedOpinion_measurable H c d g Z hg hZ
  have hInt : ∀ n i j, Integrable (fun ω => |clippedOpinion G c d (f ω) (W ω) n i -
      clippedOpinion H c d (g ω) (Z ω) n j|) μ := by
    intro n i j
    exact bounded_difference_integrable μ (hFm n i) (hGm n j)
      (fun ω => clippedOpinion_mem G c d (f ω) (W ω) n i)
      (fun ω => clippedOpinion_mem H c d (g ω) (Z ω) n j)
  intro n
  induction n with
  | zero =>
    intro i j hij
    have h := (integral_clip_difference_le μ (hf i) (hg j) (hinit i j hij).1).trans (hinit i j hij).2
    simpa only [clippedOpinion,Nat.cast_zero,zero_add,one_mul,zero_mul,add_zero] using h
  | succ n ih =>
    intro i j hij
    let E : ℝ := ((n:ℝ)+1)*η+(n:ℝ)*ε
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hstep := expected_step_bound μ (range (G.deg i)) (G.wt i) (H.wt j) (1-c-d) E η ε
      (fun r ω => clippedOpinion G c d (f ω) (W ω) n (G.nbr i r))
      (fun r ω => clippedOpinion H c d (g ω) (Z ω) n (H.nbr j r))
      (fun ω => clippedOpinion G c d (f ω) (W ω) n i)
      (fun ω => clippedOpinion H c d (g ω) (Z ω) n j)
      (fun ω => W ω n i) (fun ω => Z ω n j)
      (fun r _ => hFm n _) (fun r _ => hGm n _) (hFm n i) (hGm n j) (hW n i) (hZ n j)
      (fun r hr => (hG.1 i r (mem_range.mp hr)).1) (by linarith)
      (fun ω r _ => abs_le.mpr (clippedOpinion_mem H c d (g ω) (Z ω) n (H.nbr j r)))
      (fun r _ => hInt n _ _) (hInt n i j) (hsig n i j hij).1
      (fun r hr => ih _ _ (hnbr n i j hij r (mem_range.mp hr)))
      (ih i j (hstay n i j hij)) (hsig n i j hij).2 (hwt n i j hij)
    have hcoef : (∑ r ∈ range (G.deg i),G.wt i r) + (1-c-d) ≤ 1 := by
      have := weight_sum_le G hG hc i
      linarith
    have hbound : ((∑ r ∈ range (G.deg i),G.wt i r)+(1-c-d))*E+ε+η ≤ E+ε+η := by
      nlinarith
    have hfinal := hstep.trans hbound
    have heq : E+ε+η = (((n+1:ℕ):ℝ)+1)*η+((n+1:ℕ):ℝ)*ε := by dsimp [E]; push_cast; ring
    rw [heq] at hfinal
    simpa only [clippedOpinion,Δ,hdeg n i j hij] using hfinal

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem auxiliaryTrajectoryLaw_supported {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) :
    ∀ᵐ y ∂(auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ)),
      ∀ r, y r ∈ Icc (-1:ℝ) 1 := by
  apply (ae_map_iff (auxiliaryTrajectory_measurable ζ φ hζ hφ c d k).aemeasurable ?_).mpr
  · exact Filter.Eventually.of_forall fun p r => auxiliaryOpinion_mem ζ φ c d p.1 p.2 r 0
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun r => isClosed_Icc.measurableSet.preimage (measurable_pi_apply r)

theorem strongCoupling_limit_probability {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (μ : Measure (LimGraph A))
    (h : StrongCoupling P S 𝓖 μ) : IsProbabilityMeasure μ := by
  obtain ⟨H, H', E, E', hH, hH', hLaw, hrest⟩ := h 1 le_rfl 1 (by norm_num)
  exact (hLaw 0).isProbabilityMeasure_iff.mp inferInstance

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem transport_exists_coupling_of_le {X : Type*} [MeasurableSpace X]
    (c : X → X → ℝ≥0∞) {μ ν : Measure X} {B η : ℝ}
    (hB : 0 ≤ B) (hη : 0 < η)
    (h : RWPI.SqrtLasso.transportCost c μ ν ≤ ENNReal.ofReal B) :
    ∃ π, IsCoupling π μ ν ∧
      (∫⁻ z, c z.1 z.2 ∂π) < ENNReal.ofReal (B + η) := by
  apply transport_exists_coupling_lt c
  exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))

theorem coupling_integral_test_bound {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {π : Measure (X × X)} (hπ : IsCoupling π μ ν)
    {f : X → ℝ} (hf : Measurable f) (hμ : Integrable f μ) (hν : Integrable f ν)
    {g : X × X → ℝ} (hg : Integrable g π)
    (hbound : ∀ᵐ z ∂π, |f z.1 - f z.2| ≤ g z) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ ∫ z, g z ∂π := by
  have hμ' : Integrable f (π.map Prod.fst) := hπ.2.1.symm ▸ hμ
  have hν' : Integrable f (π.map Prod.snd) := hπ.2.2.symm ▸ hν
  have hleft : Integrable (fun z : X × X => f z.1) π :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 hμ'
  have hright : Integrable (fun z : X × X => f z.2) π :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).1 hν'
  have hIl : (∫ z : X × X, f z.1 ∂π) = ∫ x, f x ∂μ := by
    rw [← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable, hπ.2.1]
  have hIr : (∫ z : X × X, f z.2 ∂π) = ∫ x, f x ∂ν := by
    rw [← integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable, hπ.2.2]
  calc
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| = |∫ z, f z.1 - f z.2 ∂π| := by
      rw [integral_sub hleft hright, hIl, hIr]
    _ ≤ ∫ z, |f z.1 - f z.2| ∂π := abs_integral_le_integral_abs
    _ ≤ ∫ z, g z ∂π := integral_mono_ae (hleft.sub hright).abs hg hbound

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def clippedKernel {A : Type*} (ψ : Mark A → ℝ → ℝ) : Mark A → ℝ → ℝ :=
  fun x u => clip (-1) 1 (ψ x u)

theorem clippedKernel_measurable {A : Type*} [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) :
    Measurable (Function.uncurry (clippedKernel ψ)) :=
  (continuous_clip (-1) 1).measurable.comp hψ

theorem clippedKernel_map {A : Type*} [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) (x : Mark A) :
    kernelLaw (clippedKernel ψ) x = (kernelLaw ψ x).map (clip (-1) 1) := by
  unfold kernelLaw
  rw [Measure.map_map (continuous_clip (-1) 1).measurable
    (show Measurable (ψ x) from hψ.comp (measurable_const.prodMk measurable_id))]
  rfl

theorem clippedKernel_supported {A : Type*} [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) (x : Mark A) :
    ∀ᵐ y ∂kernelLaw (clippedKernel ψ) x, y ∈ Icc (-1:ℝ) 1 := by
  rw [clippedKernel_map hψ x]
  exact (ae_map_iff (continuous_clip (-1) 1).measurable.aemeasurable
    isClosed_Icc.measurableSet).mpr (Filter.Eventually.of_forall (clip_mem (by norm_num)))

theorem clippedKernel_W1_le {A : Type*} [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) (x y : Mark A) :
    W1 (kernelLaw (clippedKernel ψ) x) (kernelLaw (clippedKernel ψ) y) ≤
      W1 (kernelLaw ψ x) (kernelLaw ψ y) := by
  rw [clippedKernel_map hψ x,clippedKernel_map hψ y]
  apply transport_map_le _ _ (by fun_prop) _ _ (continuous_clip (-1) 1).measurable
    (continuous_clip (-1) 1).measurable
  intro u v
  exact ENNReal.ofReal_le_ofReal (clip_lipschitz_abs (-1) 1 u v)

theorem clippedKernel_coupling {A : Type*} [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) (x y : Mark A)
    {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η)
    (hW : W1 (kernelLaw ψ x) (kernelLaw ψ y) ≤ ENNReal.ofReal B) :
    ∃ π : Measure (ℝ × ℝ),
      IsCoupling π (kernelLaw (clippedKernel ψ) x) (kernelLaw (clippedKernel ψ) y) ∧
      Integrable (fun z => |z.1-z.2|) π ∧ (∫ z, |z.1-z.2| ∂π) < B+η := by
  obtain ⟨π,hπ,hcost⟩ := transport_exists_coupling_of_le
    (fun u v : ℝ => ENNReal.ofReal |u-v|) hB hη ((clippedKernel_W1_le hψ x y).trans hW)
  let : IsProbabilityMeasure π := hπ.1
  have hx : ∀ᵐ z ∂π, z.1 ∈ Icc (-1:ℝ) 1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact clippedKernel_supported hψ x
  have hy : ∀ᵐ z ∂π, z.2 ∈ Icc (-1:ℝ) 1 := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact clippedKernel_supported hψ y
  have hi : Integrable (fun z : ℝ × ℝ => |z.1-z.2|) π := by
    apply Integrable.of_bound (by fun_prop) 2
    filter_upwards [hx,hy] with z hz hz'
    rw [Real.norm_eq_abs,abs_abs]
    exact abs_le.mpr ⟨by linarith [hz.1,hz'.2],by linarith [hz.2,hz'.1]⟩
  refine ⟨π,hπ,hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => abs_nonneg _)] at hcost
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hcost

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

theorem rho_symmetric {A : Type*} [PseudoMetricSpace A] (x y : Mark A) : ρ x y = ρ y x := by
  simp only [ρ,dist_comm,abs_sub_comm]

theorem canonical_rho_from_valid {A : Type*} [PseudoMetricSpace A] (x y : Mark A)
    (hx : x ∈ markSpace A) : ρ x (canonicalMark y) ≤ 2*ρ x y := by
  rw [rho_symmetric x (canonicalMark y)]
  simpa only [rho_symmetric y x] using canonical_rho_le y x hx

theorem weight_l1_le_rho {A : Type*} [PseudoMetricSpace A] (x y : Mark A)
    (hdeg : x.deg = y.deg) : (∑ j ∈ range x.deg, |x.wt j-y.wt j|) ≤ ρ x y := by
  have he : (∑' j, |truncatedWeight x j-truncatedWeight y j|) =
      ∑ j ∈ range x.deg, |x.wt j-y.wt j| := by
    rw [weight_difference_sum,←hdeg,max_self]
    apply sum_congr rfl
    intro j hj
    have hxj := Finset.mem_range.mp hj
    have hyj : j < y.deg := hdeg ▸ hxj
    simp only [truncatedWeight,if_pos hxj,if_pos hyj]
  change _ ≤ dist x.attr y.attr + |x.q-y.q| + |x.s-y.s| + |(x.deg:ℝ)-y.deg| +
    (∑' j, |truncatedWeight x j-truncatedWeight y j|)
  rw [he]
  have h1 := dist_nonneg (x:=x.attr) (y:=y.attr)
  have h2 := abs_nonneg (x.q-y.q)
  have h3 := abs_nonneg (x.s-y.s)
  have h4 := abs_nonneg ((x.deg:ℝ)-y.deg)
  linarith

theorem nearby_clipped_kernel_coupling {A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    {ψ : Mark A → ℝ → ℝ} (hψ : Measurable (Function.uncurry ψ)) {K ε η : ℝ}
    (hK : KernelLipschitz ψ K) (hε : 0 ≤ ε) (hη : 0 < η)
    (x y : Mark A) (hx : x ∈ markSpace A) (hxy : ρ x y ≤ ε) :
    ∃ π : Measure (ℝ × ℝ),
      IsCoupling π (kernelLaw (clippedKernel ψ) x) (kernelLaw (clippedKernel ψ) (canonicalMark y)) ∧
      Integrable (fun z => |z.1-z.2|) π ∧
      (∫ z, |z.1-z.2| ∂π) < 2 * (max K 0) * ε + η := by
  apply clippedKernel_coupling hψ x (canonicalMark y) (by positivity) hη
  apply (kernelLipschitz_nonnegative_constant hK x hx (canonicalMark y) (canonicalMark_mem y)).trans
  apply ENNReal.ofReal_le_ofReal
  have hr := (canonical_rho_from_valid x y hx).trans (mul_le_mul_of_nonneg_left hxy (by norm_num))
  have hm := mul_le_mul_of_nonneg_left hr (le_max_right K 0)
  nlinarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Set

def matchingRelation {V A : Type*} (G : WDigraph V) (v : V) (H : LimGraph A) (k : ℕ)
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (n : ℕ) (i : V) (j : ℕ) : Prop :=
  n ≤ k ∧ ∃ x : inBall H.toWDigraph 0 k,
    (x : ℕ) = j ∧ (θ x : V) = i ∧ (x : ℕ) ∈ inBall H.toWDigraph 0 (k-n)

theorem matchingRelation_stay {V A : Type*} (G : WDigraph V) (v : V) (H : LimGraph A) (k : ℕ)
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (n : ℕ) (i : V) (j : ℕ)
    (h : matchingRelation G v H k θ (n+1) i j) : matchingRelation G v H k θ n i j := by
  obtain ⟨hn,x,hx,hi,hball⟩ := h
  refine ⟨by omega,x,hx,hi,?_⟩
  exact inBall_mono H.toWDigraph 0 (by omega) hball

theorem matchingRelation_degree_neighbor {V A : Type*} (G : WDigraph V) (v : V)
    (H : LimGraph A) (k : ℕ) (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (hθ : ∀ x : inBall H.toWDigraph 0 k,
      (∃ l < k, (x:ℕ) ∈ inBall H.toWDigraph 0 l) →
      G.deg (θ x) = (H.2 x).deg ∧ ∀ r < (H.2 x).deg,
        ∀ y : inBall H.toWDigraph 0 k, (y:ℕ)=H.1 x r → G.nbr (θ x) r = (θ y:V))
    (n : ℕ) (i : V) (j : ℕ) (h : matchingRelation G v H k θ (n+1) i j) :
    G.deg i = H.toWDigraph.deg j ∧ ∀ r < G.deg i,
      matchingRelation G v H k θ n (G.nbr i r) (H.toWDigraph.nbr j r) := by
  obtain ⟨hn,x,hx,hi,hball⟩ := h
  have hd := hθ x ⟨k-(n+1),by omega,hball⟩
  have hdeg : G.deg i = (H.2 j).deg := by simpa only [hx,hi] using hd.1
  refine ⟨hdeg,?_⟩
  intro r hr
  have hr' : r < (H.2 x).deg := by simpa only [hx,←hdeg] using hr
  have hnext : H.1 x r ∈ inBall H.toWDigraph 0 (k-n) := by
    have ht := neighbor_mem_inBall H.toWDigraph 0 x (k-(n+1)) r hball hr'
    have heq : k-(n+1)+1=k-n := by omega
    simpa only [heq,LimGraph.toWDigraph] using ht
  let y : inBall H.toWDigraph 0 k := ⟨H.1 x r,inBall_mono H.toWDigraph 0 (by omega) hnext⟩
  refine ⟨by omega,y,?_,?_,hnext⟩
  · change H.1 x r = H.1 j r
    rw [hx]
  · have he := hd.2 r hr' y rfl
    simpa only [hi] using he.symm

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

theorem paired_box_expected {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (G : WDigraph V) (v : V) (H : LimGraph A)
    (k : ℕ) [Fintype (inBall H.toWDigraph 0 k)]
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (hroot : ∀ x : inBall H.toWDigraph 0 k,(x:ℕ)=0 → (θ x:V)=v)
    (hθ : ∀ x : inBall H.toWDigraph 0 k,
      (∃ l < k,(x:ℕ) ∈ inBall H.toWDigraph 0 l) →
      G.deg (θ x)=(H.2 x).deg ∧ ∀ r<(H.2 x).deg,
        ∀ y : inBall H.toWDigraph 0 k,(y:ℕ)=H.1 x r → G.nbr (θ x) r=(θ y:V))
    (c d ε η : ℝ) (hG : G.Valid c) (hc : 0≤c) (hd : 0≤d) (hcd : c+d≤1)
    (hε : 0≤ε) (hη : 0≤η)
    (hweight : ∀ n i j, matchingRelation G v H k θ (n+1) i j →
      (∑ r ∈ range (G.deg i),|G.wt i r-(canonicalGraph H).wt j r|) ≤ ε)
    (π : SignalSlot (inBall H.toWDigraph 0 k) k → Measure (ℝ × ℝ))
    [∀ p,IsProbabilityMeasure (π p)]
    (hi : ∀ p,Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (π p))
    (hb : ∀ p,(∫ z,|z.1-z.2| ∂π p) ≤ η) (n : ℕ) (hn : n≤k) :
    (∫ u, |clippedOpinion G c d
        (boxInitial (inBall G v k) k (pairedBoxLeft θ k u))
        (boxSignals (inBall G v k) k (pairedBoxLeft θ k u)) n v -
      clippedOpinion (canonicalGraph H) c d
        (boxInitial (inBall H.toWDigraph 0 k) k (pairedBoxRight (inBall H.toWDigraph 0 k) k u))
        (boxSignals (inBall H.toWDigraph 0 k) k (pairedBoxRight (inBall H.toWDigraph 0 k) k u)) n 0|
      ∂Measure.pi π) ≤ ((n:ℝ)+1)*η+(n:ℝ)*ε := by
  apply local_expected_comparison (Measure.pi π) G (canonicalGraph H) c d ε η hG hc hd hcd hε hη
    (fun u => boxInitial (inBall G v k) k (pairedBoxLeft θ k u))
    (fun u => boxInitial (inBall H.toWDigraph 0 k) k (pairedBoxRight (inBall H.toWDigraph 0 k) k u))
    (fun u => boxSignals (inBall G v k) k (pairedBoxLeft θ k u))
    (fun u => boxSignals (inBall H.toWDigraph 0 k) k (pairedBoxRight (inBall H.toWDigraph 0 k) k u))
    (fun i => (boxInitial_measurable _ _ i).comp (pairedBoxLeft_measurable θ k))
    (fun i => (boxInitial_measurable _ _ i).comp (pairedBoxRight_measurable _ k))
    (fun t i => (boxSignals_measurable _ _ t i).comp (pairedBoxLeft_measurable θ k))
    (fun t i => (boxSignals_measurable _ _ t i).comp (pairedBoxRight_measurable _ k))
    (matchingRelation G v H k θ)
    (matchingRelation_stay G v H k θ)
    (fun t i j hr => (matchingRelation_degree_neighbor G v H k θ hθ t i j hr).1)
    (fun t i j hr => (matchingRelation_degree_neighbor G v H k θ hθ t i j hr).2)
    hweight
  · intro i j hr
    obtain ⟨_,x,rfl,rfl,_⟩ := hr
    exact paired_initial_cost θ k π hi hb x
  · intro t i j hr
    obtain ⟨ht,x,rfl,rfl,_⟩ := hr
    exact paired_signal_cost θ k π hi hb t (by omega) x
  · refine ⟨hn,⟨0,root_mem_inBall _ _ _⟩,rfl,hroot _ rfl,?_⟩
    exact root_mem_inBall _ _ _

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Set Finset

theorem fullMark_mem {V A : Type*} (G : WDigraph V) {c : ℝ} (hG : G.Valid c)
    (Y : V → A × ℝ × ℝ) (hq : ∀ i,(Y i).2.1 ∈ Icc (-1:ℝ) 1)
    (hs : ∀ i,(Y i).2.2=0 ∨ (Y i).2.2=1) (i : V) : fullMark G (Y i) i ∈ markSpace A := by
  refine ⟨hq i,hs i,?_⟩
  intro r
  change (if r<G.deg i then G.wt i r else 0) ∈ Icc (0:ℝ) 1
  split_ifs with hr
  · exact hG.1 i r hr
  · norm_num

theorem matching_weight_bound {V A : Type*} [PseudoMetricSpace A]
    (G : WDigraph V) {c ε : ℝ} (hG : G.Valid c) (Y : V → A × ℝ × ℝ)
    (hq : ∀ i,(Y i).2.1 ∈ Icc (-1:ℝ) 1) (hs : ∀ i,(Y i).2.2=0 ∨ (Y i).2.2=1)
    (v : V) (H : LimGraph A) (k : ℕ) (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (hdegree : ∀ n i j, matchingRelation G v H k θ (n+1) i j → G.deg i=(H.2 j).deg)
    (hρ : ∀ x : inBall H.toWDigraph 0 k, ρ (fullMark G (Y (θ x)) (θ x)) (H.2 x) ≤ ε)
    (n : ℕ) (i : V) (j : ℕ) (hR : matchingRelation G v H k θ (n+1) i j) :
    (∑ r ∈ range (G.deg i),|G.wt i r-(canonicalGraph H).wt j r|) ≤ 2*ε := by
  have hd := hdegree n i j hR
  obtain ⟨_,x,hx,hi,_⟩ := hR
  have hr : ρ (fullMark G (Y i) i) (H.2 j) ≤ ε := by simpa only [hx,hi] using hρ x
  have hcanon := (canonical_rho_from_valid (fullMark G (Y i) i) (H.2 j)
    (fullMark_mem G hG Y hq hs i)).trans (mul_le_mul_of_nonneg_left hr (by norm_num))
  have hw := weight_l1_le_rho (fullMark G (Y i) i) (canonicalMark (H.2 j)) hd
  have he : (∑ r ∈ range (G.deg i), |G.wt i r-(canonicalGraph H).wt j r|) =
      ∑ r ∈ range (fullMark G (Y i) i).deg,
        |(fullMark G (Y i) i).wt r-(canonicalMark (H.2 j)).wt r| := by
    apply sum_congr rfl
    intro r hr
    change |G.wt i r-(canonicalMark (H.2 j)).wt r| =
      |(if r<G.deg i then G.wt i r else 0)-(canonicalMark (H.2 j)).wt r|
    rw [if_pos (Finset.mem_range.mp hr)]
  rw [he]
  exact hw.trans hcanon

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

def slotFunction {A : Type*} {k : ℕ} (ζ φ : Mark A → ℝ → ℝ) : Option (Fin k) → Mark A → ℝ → ℝ
  | none => φ
  | some _ => ζ

noncomputable def leftSignalLaw {V A : Type*} [MeasurableSpace A]
    (G : WDigraph V) (Y : V → A × ℝ × ℝ) (v : V) (H : LimGraph A) (k : ℕ)
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (ζ φ : Mark A → ℝ → ℝ)
    (p : SignalSlot (inBall H.toWDigraph 0 k) k) : Measure ℝ :=
  kernelLaw (clippedKernel (slotFunction ζ φ p.1)) (fullMark G (Y (θ p.2)) (θ p.2))

noncomputable def rightSignalLaw {A : Type*} [MeasurableSpace A]
    (H : LimGraph A) (k : ℕ) (ζ φ : Mark A → ℝ → ℝ)
    (p : SignalSlot (inBall H.toWDigraph 0 k) k) : Measure ℝ :=
  kernelLaw (clippedKernel (slotFunction ζ φ p.1)) (canonicalMark (H.2 p.2))

theorem signal_box_couplings_exist {V A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    (G : WDigraph V) {c K ε η : ℝ} (hG : G.Valid c) (Y : V → A × ℝ × ℝ)
    (hq : ∀ i,(Y i).2.1 ∈ Icc (-1:ℝ) 1) (hs : ∀ i,(Y i).2.2=0 ∨ (Y i).2.2=1)
    (v : V) (H : LimGraph A) (k : ℕ) (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (hε : 0≤ε) (hη : 0<η)
    (hρ : ∀ x : inBall H.toWDigraph 0 k,ρ (fullMark G (Y (θ x)) (θ x)) (H.2 x) ≤ ε) :
    ∃ π : SignalSlot (inBall H.toWDigraph 0 k) k → Measure (ℝ × ℝ),
      (∀ p,IsCoupling (π p) (leftSignalLaw G Y v H k θ ζ φ p) (rightSignalLaw H k ζ φ p)) ∧
      (∀ p,Integrable (fun z : ℝ × ℝ => |z.1-z.2|) (π p)) ∧
      (∀ p,(∫ z,|z.1-z.2| ∂π p) < 2*max K 0*ε+η) := by
  have hh : ∀ p : SignalSlot (inBall H.toWDigraph 0 k) k,
      ∃ π : Measure (ℝ × ℝ),
      IsCoupling π (leftSignalLaw G Y v H k θ ζ φ p) (rightSignalLaw H k ζ φ p) ∧
      Integrable (fun z : ℝ × ℝ => |z.1-z.2|) π ∧ (∫ z,|z.1-z.2| ∂π) < 2*max K 0*ε+η := by
    intro p
    have hmeas : Measurable (Function.uncurry (slotFunction ζ φ p.1)) := by
      cases p.1 <;> assumption
    have hK : KernelLipschitz (slotFunction ζ φ p.1) K := by cases p.1 <;> assumption
    exact nearby_clipped_kernel_coupling hmeas hK hε hη _ _
      (fullMark_mem G hG Y hq hs _) (hρ p.2)
  choose π hπ hi hb using hh
  exact ⟨π,hπ,hi,hb⟩

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def vertexNoiseLaw (V : Type*) : Measure (Option ℕ × V → ℝ) :=
  Measure.infinitePi (fun _ : Option ℕ × V => uniformUnit)
instance vertexNoiseLaw_probability (V : Type*) : IsProbabilityMeasure (vertexNoiseLaw V) := by
  unfold vertexNoiseLaw
  infer_instance

noncomputable def fixedTrajectory {V A : Type*} (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (v : V) (u : Option ℕ × V → ℝ) :
    Fin (k+1) → ℝ := fun r => clippedOpinion G c d
      (fun i => φ (ξ i) (u (none,i))) (fun t i => ζ (ξ i) (u (some t,i))) r v

theorem fixedTrajectory_measurable {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [MeasurableSpace A] (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (v : V) :
    Measurable (fixedTrajectory G ξ ζ φ c d k v) := by
  apply measurable_pi_lambda
  intro r
  apply fixed_clippedOpinion_measurable
  · intro i
    exact hφ.comp (measurable_const.prodMk (measurable_pi_apply (none,i)))
  · intro t i
    exact hζ.comp (measurable_const.prodMk (measurable_pi_apply (some t,i)))

noncomputable def sampledSignalBox {V A : Type*} (S : Set V) (k : ℕ) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (u : Option ℕ × V → ℝ) : SignalSlot S k → ℝ :=
  fun p => clippedKernel (slotFunction ζ φ p.1) (ξ p.2) (u (boxNoiseEmbedding S k p))

theorem sampledSignalBox_hasLaw {V A : Type*} [MeasurableSpace A] (S : Set V) [Fintype S]
    (k : ℕ) (ξ : V → Mark A) (ζ φ : Mark A → ℝ → ℝ)
    (hζ : Measurable (Function.uncurry ζ)) (hφ : Measurable (Function.uncurry φ)) :
    HasLaw (sampledSignalBox S k ξ ζ φ)
      (Measure.pi (fun p : SignalSlot S k => kernelLaw (clippedKernel (slotFunction ζ φ p.1)) (ξ p.2)))
      (vertexNoiseLaw V) := by
  apply finite_signal_sample_law (boxNoiseEmbedding S k) (boxNoiseEmbedding_injective S k)
  intro p
  have hm : Measurable (Function.uncurry (slotFunction ζ φ p.1)) := by cases p.1 <;> assumption
  exact (clippedKernel_measurable hm).comp (measurable_const.prodMk measurable_id)

theorem sampledSignalBox_values {V A : Type*} (S : Set V) (k : ℕ) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (u : Option ℕ × V → ℝ) :
    sampledSignalBox S k ξ ζ φ u = boxValues S k
      (fun i => clip (-1) 1 (φ (ξ i) (u (none,i))))
      (fun t i => clip (-1) 1 (ζ (ξ i) (u (some t,i)))) := by
  funext p
  rcases p with ⟨t,i⟩
  cases t <;> rfl

theorem sampledSignalBox_trajectory {V A : Type*} (G : WDigraph V) (v : V) (S : Set V)
    (k : ℕ) (hS : inBall G v k ⊆ S) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (u : Option ℕ × V → ℝ) :
    boxTrajectory G v S c d k (sampledSignalBox S k ξ ζ φ u) = fixedTrajectory G ξ ζ φ c d k v u := by
  rw [sampledSignalBox_values]
  funext r
  change clippedOpinion G c d _ _ r v = _
  rw [box_opinion_eq G c d v S k r (by omega) hS]
  exact congrFun (clippedOpinion_clip_inputs G c d _ _ r) v

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

def reindexBox {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ)
    (x : SignalSlot S k → ℝ) : SignalSlot T k → ℝ := fun p => x (p.1,θ.symm p.2)

theorem reindexBox_measurable {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ) :
    Measurable (reindexBox θ k) := by unfold reindexBox; fun_prop

def matchedNoiseEmbedding {V U : Type*} {S : Set V} {T : Set U} (θ : S ≃ T) (k : ℕ)
    (p : SignalSlot S k) : Option ℕ × U := (p.1.map Fin.val,(θ p.2).val)

theorem matchedNoiseEmbedding_injective {V U : Type*} {S : Set V} {T : Set U}
    (θ : S ≃ T) (k : ℕ) : Function.Injective (matchedNoiseEmbedding θ k) := by
  intro p q hp
  have h1 : p.1.map Fin.val=q.1.map Fin.val := congrArg Prod.fst hp
  have h2 : (θ p.2).val=(θ q.2).val := congrArg Prod.snd hp
  exact Prod.ext (Option.map_injective Fin.val_injective h1) (θ.injective (Subtype.ext h2))

noncomputable def matchedSignalSample {V A : Type*} (G : WDigraph V) (Y : V → A × ℝ × ℝ)
    (v : V) (H : LimGraph A) (k : ℕ) (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (ζ φ : Mark A → ℝ → ℝ) (u : Option ℕ × V → ℝ) : SignalSlot (inBall H.toWDigraph 0 k) k → ℝ :=
  fun p => clippedKernel (slotFunction ζ φ p.1) (fullMark G (Y (θ p.2)) (θ p.2))
    (u (matchedNoiseEmbedding θ k p))

theorem matchedSignalSample_hasLaw {V A : Type*} [MeasurableSpace A] (G : WDigraph V)
    (Y : V → A × ℝ × ℝ) (v : V) (H : LimGraph A) (k : ℕ) [Fintype (inBall H.toWDigraph 0 k)]
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (ζ φ : Mark A → ℝ → ℝ)
    (hζ : Measurable (Function.uncurry ζ)) (hφ : Measurable (Function.uncurry φ)) :
    HasLaw (matchedSignalSample G Y v H k θ ζ φ) (Measure.pi (leftSignalLaw G Y v H k θ ζ φ))
      (vertexNoiseLaw V) := by
  apply finite_signal_sample_law (matchedNoiseEmbedding θ k) (matchedNoiseEmbedding_injective θ k)
  intro p
  have hm : Measurable (Function.uncurry (slotFunction ζ φ p.1)) := by cases p.1 <;> assumption
  exact (clippedKernel_measurable hm).comp (measurable_const.prodMk measurable_id)

theorem matchedSignalSample_reindex {V A : Type*} (G : WDigraph V) (Y : V → A × ℝ × ℝ)
    (v : V) (H : LimGraph A) (k : ℕ) (θ : inBall H.toWDigraph 0 k ≃ inBall G v k)
    (ζ φ : Mark A → ℝ → ℝ) (u : Option ℕ × V → ℝ) :
    reindexBox θ k (matchedSignalSample G Y v H k θ ζ φ u) =
      sampledSignalBox (inBall G v k) k (fun i => fullMark G (Y i) i) ζ φ u := by
  funext p
  simp only [reindexBox,matchedSignalSample,sampledSignalBox,matchedNoiseEmbedding,
    boxNoiseEmbedding,Equiv.apply_symm_apply]

theorem canonicalGraph_inBall {A : Type*} (H : LimGraph A) (v : ℕ) :
    ∀ k,inBall (canonicalGraph H) v k = inBall H.toWDigraph v k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    change (inBall (canonicalGraph H) v k ∪ {u | ∃ w ∈ inBall (canonicalGraph H) v k, ∃ r < (canonicalGraph H).deg w, (canonicalGraph H).nbr w r = u}) = _
    change _ = (inBall H.toWDigraph v k ∪ {u | ∃ w ∈ inBall H.toWDigraph v k, ∃ r < H.toWDigraph.deg w, H.toWDigraph.nbr w r = u})
    rw [ih]
    rfl

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

theorem product_first_law {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ ν : I → Measure X) (π : I → Measure (X × X))
    (hπ : ∀ i,IsCoupling (π i) (μ i) (ν i)) :
    HasLaw (fun u : I → X × X => fun i => (u i).1) (Measure.pi μ) (Measure.pi π) := by
  let : ∀ i,IsProbabilityMeasure (π i) := fun i => (hπ i).1
  refine ⟨(by fun_prop : Measurable (fun u : I → X × X => fun i => (u i).1)).aemeasurable,?_⟩
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  congr 1
  funext i
  exact (hπ i).2.1

theorem product_second_law {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ ν : I → Measure X) (π : I → Measure (X × X))
    (hπ : ∀ i,IsCoupling (π i) (μ i) (ν i)) :
    HasLaw (fun u : I → X × X => fun i => (u i).2) (Measure.pi ν) (Measure.pi π) := by
  let : ∀ i,IsProbabilityMeasure (π i) := fun i => (hπ i).1
  refine ⟨(by fun_prop : Measurable (fun u : I → X × X => fun i => (u i).2)).aemeasurable,?_⟩
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  congr 1
  funext i
  exact (hπ i).2.2

theorem same_law_test_integral {Ω Ξ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace X] {P : Measure Ω} {Q : Measure Ξ} {μ : Measure X}
    {F : Ω → X} {G : Ξ → X} (hF : HasLaw F μ P) (hG : HasLaw G μ Q)
    {f : X → ℝ} (hf : Measurable f) :
    (∫ ω,f (F ω) ∂P) = ∫ ω,f (G ω) ∂Q := by
  simpa only [Function.comp_def] using
    (hF.integral_comp hf.aestronglyMeasurable).trans (hG.integral_comp hf.aestronglyMeasurable).symm

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def fixedTestExpectation {V A : Type*} (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (v : V) (f : FiniteCube k → ℝ) : ℝ :=
  ∫ u,f (cubeRetraction k (fixedTrajectory G ξ ζ φ c d k v u)) ∂vertexNoiseLaw V

noncomputable def limitTestExpectation {A : Type*} (H : LimGraph A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (f : FiniteCube k → ℝ) : ℝ :=
  fixedTestExpectation (canonicalGraph H) (fun i => canonicalMark (H.2 i)) ζ φ c d k 0 f

theorem left_box_test_integral {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [MeasurableSpace A] (G : WDigraph V)
    (Y : V → A × ℝ × ℝ) (v : V) (H : LimGraph A) (k : ℕ) [Fintype (inBall H.toWDigraph 0 k)]
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (ζ φ : Mark A → ℝ → ℝ)
    (hζ : Measurable (Function.uncurry ζ)) (hφ : Measurable (Function.uncurry φ)) (c d : ℝ)
    (π : SignalSlot (inBall H.toWDigraph 0 k) k → Measure (ℝ × ℝ))
    (hπ : ∀ p,IsCoupling (π p) (leftSignalLaw G Y v H k θ ζ φ p) (rightSignalLaw H k ζ φ p))
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (∫ u,f (cubeRetraction k (boxTrajectory G v (inBall G v k) c d k (pairedBoxLeft θ k u))) ∂Measure.pi π) =
      fixedTestExpectation G (fun i => fullMark G (Y i) i) ζ φ c d k v f := by
  let T : (SignalSlot (inBall H.toWDigraph 0 k) k → ℝ) → ℝ :=
    fun x => f (cubeRetraction k (boxTrajectory G v (inBall G v k) c d k (reindexBox θ k x)))
  have hT : Measurable T := hf.measurable.comp ((cubeRetraction_continuous k).measurable.comp
    ((boxTrajectory_measurable G v (inBall G v k) c d k).comp (reindexBox_measurable θ k)))
  have he := same_law_test_integral (product_first_law _ _ π hπ)
    (matchedSignalSample_hasLaw G Y v H k θ ζ φ hζ hφ) hT
  calc
    _ = ∫ u,T (matchedSignalSample G Y v H k θ ζ φ u) ∂vertexNoiseLaw V := he
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp [T]
      rw [matchedSignalSample_reindex,sampledSignalBox_trajectory G v (inBall G v k) k (fun _ h => h)]

theorem right_box_test_integral {V A : Type*} [MeasurableSpace A] (G : WDigraph V)
    (Y : V → A × ℝ × ℝ) (v : V) (H : LimGraph A) (k : ℕ) [Fintype (inBall H.toWDigraph 0 k)]
    (θ : inBall H.toWDigraph 0 k ≃ inBall G v k) (ζ φ : Mark A → ℝ → ℝ)
    (hζ : Measurable (Function.uncurry ζ)) (hφ : Measurable (Function.uncurry φ)) (c d : ℝ)
    (π : SignalSlot (inBall H.toWDigraph 0 k) k → Measure (ℝ × ℝ))
    (hπ : ∀ p,IsCoupling (π p) (leftSignalLaw G Y v H k θ ζ φ p) (rightSignalLaw H k ζ φ p))
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (∫ u,f (cubeRetraction k (boxTrajectory (canonicalGraph H) 0 (inBall H.toWDigraph 0 k) c d k
      (pairedBoxRight (inBall H.toWDigraph 0 k) k u))) ∂Measure.pi π) =
      limitTestExpectation H ζ φ c d k f := by
  let T : (SignalSlot (inBall H.toWDigraph 0 k) k → ℝ) → ℝ :=
    fun x => f (cubeRetraction k (boxTrajectory (canonicalGraph H) 0 (inBall H.toWDigraph 0 k) c d k x))
  have hT : Measurable T := hf.measurable.comp ((cubeRetraction_continuous k).measurable.comp
    (boxTrajectory_measurable (canonicalGraph H) 0 (inBall H.toWDigraph 0 k) c d k))
  have he := same_law_test_integral (product_second_law _ _ π hπ)
    (sampledSignalBox_hasLaw (inBall H.toWDigraph 0 k) k (fun i => canonicalMark (H.2 i)) ζ φ hζ hφ) hT
  calc
    _ = ∫ u,T (sampledSignalBox (inBall H.toWDigraph 0 k) k (fun i => canonicalMark (H.2 i)) ζ φ u)
        ∂vertexNoiseLaw ℕ := he
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp [T]
      have hs : inBall (canonicalGraph H) 0 k ⊆ inBall H.toWDigraph 0 k := by rw [canonicalGraph_inBall]
      rw [sampledSignalBox_trajectory (canonicalGraph H) 0 (inBall H.toWDigraph 0 k) k hs]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

def decodeNativeGraph {A : Type*} {m : ℕ} (z : NativeGraphData A m) : WDigraph (Fin (m+1)) :=
  ⟨z.1, z.2.1, z.2.2.1⟩

def decodeNativeMark {A : Type*} {m : ℕ} (z : NativeGraphData A m) (i : Fin (m+1)) : Mark A :=
  fullMark (decodeNativeGraph z) (z.2.2.2 i) i

theorem decodeNativeMark_measurable {A : Type*} [MeasurableSpace A] (m : ℕ) (i : Fin (m+1)) :
    Measurable (fun z : NativeGraphData A m => decodeNativeMark z i) := by
  have ha : Measurable (fun z : NativeGraphData A m => z.2.2.2 i) := by fun_prop
  have hd : Measurable (fun z : NativeGraphData A m => z.1 i) := by fun_prop
  have hw : Measurable (fun z : NativeGraphData A m => fun r =>
      if r < z.1 i then z.2.2.1 i r else 0) := by
    apply measurable_pi_lambda
    intro r
    exact (by fun_prop : Measurable (fun z : NativeGraphData A m => z.2.2.1 i r)).piecewise (measurableSet_lt measurable_const hd) measurable_const
  exact ha.fst.prodMk (ha.snd.fst.prodMk (ha.snd.snd.prodMk (hd.prodMk hw)))

noncomputable def nativeKernelOpinion {A : Type*} {m : ℕ} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (z : NativeGraphData A m) (u : Option ℕ × Fin (m+1) → ℝ) (k : ℕ) (i : Fin (m+1)) : ℝ :=
  clippedOpinion (decodeNativeGraph z) c d
    (fun j => φ (decodeNativeMark z j) (u (none,j)))
    (fun t j => ζ (decodeNativeMark z j) (u (some t,j))) k i

theorem nativeKernelOpinion_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (i : Fin (m+1)) :
    Measurable (fun p : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) =>
      nativeKernelOpinion ζ φ c d p.1 p.2 k i) := by
  apply clippedOpinion_measurable
  · intro j; exact measurable_fst.fst.eval
  · intro j r; exact measurable_fst.snd.fst.eval.eval
  · intro j r; exact measurable_fst.snd.snd.fst.eval.eval
  · intro j
    exact hφ.comp (((decodeNativeMark_measurable m j).comp measurable_fst).prodMk (by fun_prop))
  · intro t j
    exact hζ.comp (((decodeNativeMark_measurable m j).comp measurable_fst).prodMk (by fun_prop))

theorem nativeKernelOpinion_mem {A : Type*} {m : ℕ} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (z : NativeGraphData A m) (u : Option ℕ × Fin (m+1) → ℝ) (k : ℕ) (i : Fin (m+1)) :
    nativeKernelOpinion ζ φ c d z u k i ∈ Icc (-1:ℝ) 1 :=
  clippedOpinion_mem _ _ _ _ _ _ _

theorem nativeKernelOpinion_actual {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω)
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ) (ω : Ω) (i : Fin (m+1)) :
    nativeKernelOpinion ζ φ c d (S.graphData m ω) (fun p => S.unif m p ω) k i =
      S.R ζ φ c d m k ω i := by
  exact congrFun (clippedOpinion_eq (S.G m ω) (hS.valid m ω) hS.cd_le_one _ _
    (fun j => abs_le.mpr (hS.φ_mem _ _)) (fun t j => hS.signal_bound m t j ω) k) i

noncomputable def nativeKernelTrajectory {A : Type*} {m : ℕ} (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ)
    (z : NativeGraphData A m) (u : Option ℕ × Fin (m+1) → ℝ) (k : ℕ) (i : Fin (m+1)) :
    Fin (k+1) → ℝ := fun r => nativeKernelOpinion ζ φ c d z u r i

theorem nativeKernelTrajectory_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (i : Fin (m+1)) :
    Measurable (fun p : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) =>
      nativeKernelTrajectory ζ φ c d p.1 p.2 k i) :=
  measurable_pi_lambda _ (fun r => nativeKernelOpinion_measurable m ζ φ hζ hφ c d r i)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem limitTestExpectation_measurable {A : Type*} [MeasurableSpace A]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Measurable (fun H : LimGraph A => limitTestExpectation H ζ φ c d k f) := by
  have hh := hf.measurable.comp ((cubeRetraction_continuous k).measurable.comp
    (auxiliaryTrajectory_measurable ζ φ hζ hφ c d k))
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

theorem nativeTestExpectation_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Measurable (fun p : Fin (m+1) × NativeGraphData A m =>
      fixedTestExpectation (decodeNativeGraph p.2) (decodeNativeMark p.2) ζ φ c d k p.1 f) := by
  have hh : Measurable (fun q : (Fin (m+1) × NativeGraphData A m) ×
      (Option ℕ × Fin (m+1) → ℝ) =>
      f (cubeRetraction k (nativeKernelTrajectory ζ φ c d q.1.2 q.2 k q.1.1))) := by
    apply hf.measurable.comp
    apply (cubeRetraction_continuous k).measurable.comp
    apply measurable_pi_lambda
    intro r
    exact measurable_countable_choice
      (fun i (q : (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ)) =>
        nativeKernelOpinion ζ φ c d q.1.2 q.2 r i)
      (fun i => (nativeKernelOpinion_measurable m ζ φ hζ hφ c d r i).comp
        (measurable_fst.snd.prodMk measurable_snd)) (fun q => q.1.1) measurable_fst.fst
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

theorem compact_test_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) : ∃ M : ℝ,0≤M ∧ ∀ x,|f x|≤M := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x
  have hx : |f x|≤M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
  exact hx.trans (le_max_left _ _)

theorem integral_abs_le_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) {M : ℝ} (_hM : 0≤M) (hb : ∀ ω,|f ω|≤M) :
    |∫ ω,f ω ∂μ| ≤ M := by
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω))
    (integrable_const M : Integrable (fun _ : Ω => M) μ) (Filter.Eventually.of_forall hb)
  simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hh

theorem fixedTestExpectation_bound {V A : Type*} (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (v : V) (f : FiniteCube k → ℝ)
    {M : ℝ} (hM : 0≤M) (hb : ∀ x,|f x|≤M) :
    |fixedTestExpectation G ξ ζ φ c d k v f| ≤ M :=
  integral_abs_le_bound (vertexNoiseLaw V) _ hM (fun _ => hb _)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Finset

theorem disjoint_noise_samples {I J N : Type*} [Fintype I] [Fintype J]
    (e : I → N) (g : J → N) (hdis : ∀ i j,e i ≠ g j) :
    IndepFun (fun u : N → ℝ => fun i => u (e i))
      (fun u : N → ℝ => fun j => u (g j))
      (Measure.infinitePi (fun _ : N => uniformUnit)) := by
  classical
  let S : Finset N := Finset.univ.image e
  let T : Finset N := Finset.univ.image g
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro n hn ht
    obtain ⟨i,_,rfl⟩ := mem_image.mp hn
    obtain ⟨j,_,he⟩ := mem_image.mp ht
    exact hdis i j he.symm
  have hi : iIndepFun (fun n (u : N → ℝ) => u n)
      (Measure.infinitePi (fun _ : N => uniformUnit)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have hh := hi.indepFun_finset S T hd (fun _ => measurable_pi_apply _)
  let f : (S → ℝ) → I → ℝ := fun x i => x ⟨e i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
  let q : (T → ℝ) → J → ℝ := fun x j => x ⟨g j,mem_image.mpr ⟨j,mem_univ _,rfl⟩⟩
  exact hh.comp (by fun_prop : Measurable f) (by fun_prop : Measurable q)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem sampledSignalBoxes_indep {V A : Type*} [MeasurableSpace A]
    (S T : Set V) [Fintype S] [Fintype T] (hST : Disjoint S T) (k : ℕ)
    (ξ : V → Mark A) (ζ φ : Mark A → ℝ → ℝ)
    (hζ : Measurable (Function.uncurry ζ)) (hφ : Measurable (Function.uncurry φ)) :
    IndepFun (sampledSignalBox S k ξ ζ φ) (sampledSignalBox T k ξ ζ φ) (vertexNoiseLaw V) := by
  have hh := disjoint_noise_samples (boxNoiseEmbedding S k) (boxNoiseEmbedding T k) (by
    intro p q he
    have hv : (p.2:V)=(q.2:V) := congrArg Prod.snd he
    exact Set.disjoint_left.mp hST p.2.property (hv.symm ▸ q.2.property))
  let F := fun (x : SignalSlot S k → ℝ) p => clippedKernel (slotFunction ζ φ p.1) (ξ p.2) (x p)
  let Q := fun (x : SignalSlot T k → ℝ) p => clippedKernel (slotFunction ζ φ p.1) (ξ p.2) (x p)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro p
    have hm : Measurable (Function.uncurry (slotFunction ζ φ p.1)) := by cases p.1 <;> assumption
    exact (clippedKernel_measurable hm).comp (measurable_const.prodMk (measurable_pi_apply p))
  have hQ : Measurable Q := by
    apply measurable_pi_lambda
    intro p
    have hm : Measurable (Function.uncurry (slotFunction ζ φ p.1)) := by cases p.1 <;> assumption
    exact (clippedKernel_measurable hm).comp (measurable_const.prodMk (measurable_pi_apply p))
  exact hh.comp hF hQ

theorem disjoint_trajectory_kernels {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [MeasurableSpace A] (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (v w : V)
    (hdis : Disjoint (inBall G v k) (inBall G w k)) :
    IndepFun (fixedTrajectory G ξ ζ φ c d k v) (fixedTrajectory G ξ ζ φ c d k w)
      (vertexNoiseLaw V) := by
  classical
  let : Fintype (inBall G v k) := (inBall_finite G v k).fintype
  let : Fintype (inBall G w k) := (inBall_finite G w k).fintype
  have hh := (sampledSignalBoxes_indep (inBall G v k) (inBall G w k) hdis k ξ ζ φ hζ hφ).comp
    (boxTrajectory_measurable G v (inBall G v k) c d k)
    (boxTrajectory_measurable G w (inBall G w k) c d k)
  have he1 : (fun u => boxTrajectory G v (inBall G v k) c d k (sampledSignalBox (inBall G v k) k ξ ζ φ u)) =
      fixedTrajectory G ξ ζ φ c d k v := by
    funext u
    exact sampledSignalBox_trajectory G v (inBall G v k) k (fun _ h => h) ξ ζ φ c d u
  have he2 : (fun u => boxTrajectory G w (inBall G w k) c d k (sampledSignalBox (inBall G w k) k ξ ζ φ u)) =
      fixedTrajectory G ξ ζ φ c d k w := by
    funext u
    exact sampledSignalBox_trajectory G w (inBall G w k) k (fun _ h => h) ξ ζ φ c d u
  simpa only [Function.comp_def,he1,he2] using hh

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem disjoint_test_factorization {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [MeasurableSpace A] (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (v w : V)
    (hdis : Disjoint (inBall G v k) (inBall G w k)) (f g : FiniteCube k → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ u, f (cubeRetraction k (fixedTrajectory G ξ ζ φ c d k v u)) *
      g (cubeRetraction k (fixedTrajectory G ξ ζ φ c d k w u)) ∂vertexNoiseLaw V) =
      fixedTestExpectation G ξ ζ φ c d k v f * fixedTestExpectation G ξ ζ φ c d k w g := by
  have hi := (disjoint_trajectory_kernels G ξ ζ φ hζ hφ c d k v w hdis).comp
    (hf.measurable.comp (cubeRetraction_continuous k).measurable)
    (hg.measurable.comp (cubeRetraction_continuous k).measurable)
  exact hi.integral_mul_eq_mul_integral
    ((hf.measurable.comp (cubeRetraction_continuous k).measurable).comp
      (fixedTrajectory_measurable G ξ ζ φ hζ hφ c d k v)).aestronglyMeasurable
    ((hg.measurable.comp (cubeRetraction_continuous k).measurable).comp
      (fixedTrajectory_measurable G ξ ζ φ hζ hφ c d k w)).aestronglyMeasurable

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def nativeTrajectoryTest {A : Type*} {m : ℕ} (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (k : ℕ) (f : FiniteCube k → ℝ)
    (p : (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ)) : ℝ :=
  f (cubeRetraction k (nativeKernelTrajectory ζ φ c d p.1.2 p.2 k p.1.1))

theorem nativeTrajectoryTest_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) : Measurable (nativeTrajectoryTest (m:=m) ζ φ c d k f) := by
  apply hf.measurable.comp
  apply (cubeRetraction_continuous k).measurable.comp
  apply measurable_pi_lambda
  intro r
  exact measurable_countable_choice
    (fun i (q : (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ)) =>
      nativeKernelOpinion ζ φ c d q.1.2 q.2 r i)
    (fun i => (nativeKernelOpinion_measurable m ζ φ hζ hφ c d r i).comp
      (measurable_fst.snd.prodMk measurable_snd)) (fun q => q.1.1) measurable_fst.fst

theorem native_test_noise_average {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) ∂P) =
    ∫ ω,fixedTestExpectation (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) f ∂P := by
  let T := fun ω => (S.I m ω,S.graphData m ω)
  have hT : Measurable[𝓖 m] T := (hS.measurable_I m).prodMk (hS.measurable_graph m)
  have hm := nativeTrajectoryTest_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf
  obtain ⟨M,_hM,hb⟩ := compact_test_bound f hf
  have hi : Integrable (nativeTrajectoryTest (m:=m) ζ φ c d k f) ((P.map T).prod (finiteVertexNoiseLaw m)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable M
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs,nativeTrajectoryTest] using hb _
  have he := independent_noise_integral P (finiteVertexNoiseLaw m) T (fun ω p => S.unif m p ω)
    (hT.mono (hS.le m) le_rfl) (native_noise_hasLaw P S 𝓖 ζ φ c d hS m)
    (native_noise_indep_struct_function P S 𝓖 ζ φ c d hS m T hT).symm
    (nativeTrajectoryTest ζ φ c d k f) hm hi
  convert he using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [nativeTrajectoryTest,T]
    apply congrArg f
    apply congrArg (cubeRetraction k)
    funext r
    exact (nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m r ω (S.I m ω)).symm
  · rfl

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem native_trajectory_conditional_identity {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (fun ω => ∫ x,f (cubeRetraction k x) ∂trajCondLaw P S ζ φ c d m k ω) =ᵐ[P]
    P[(fun ω => (1/((m:ℝ)+1))*∑ i,
      f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i))) | S.𝓐 m] := by
  let K := fun i (p : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ)) =>
    nativeKernelTrajectory ζ φ c d p.1 p.2 k i
  have hK : ∀ i,Measurable (K i) := fun i =>
    nativeKernelTrajectory_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i
  let g := fun x => f (cubeRetraction k x)
  have hg : Measurable g := hf.measurable.comp (cubeRetraction_continuous k).measurable
  let D := fun ω => (S.graphData m ω,fun p => S.unif m p ω)
  have hD : Measurable D := ((hS.measurable_graph m).mono (hS.le m) le_rfl).prodMk
    (measurable_pi_lambda _ (hS.measurable_unif m))
  obtain ⟨M,_hM,hb⟩ := compact_test_bound f hf
  have hi : ∀ i,Integrable (fun ω => g (K i (D ω))) P := fun i =>
    Integrable.of_bound (hg.comp ((hK i).comp hD)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,g] using hb _)
  have hsel : Measurable (fun ω => K (S.I m ω) (D ω)) :=
    measurable_countable_choice (fun i ω => K i (D ω)) (fun i => (hK i).comp hD)
      (S.I m) ((hS.measurable_I m).mono (hS.le m) le_rfl)
  have hri : Integrable (fun ω => g (K (S.I m ω) (D ω))) P :=
    Integrable.of_bound (hg.comp hsel).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,g] using hb _)
  have hid := native_conditional_kernel_test_identity P S 𝓖 ζ φ c d hS m K hK g hg.stronglyMeasurable hi hri
  have he : ∀ i ω,K i (S.graphData m ω,fun p => S.unif m p ω) =
      fun r : Fin (k+1) => S.R ζ φ c d m r ω i := by
    intro i ω
    funext r
    exact nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m r ω i
  simpa only [he,g,trajCondLaw,Fintype.card_fin,Nat.cast_add,Nat.cast_one,one_div] using hid

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem auxiliary_test_integral {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (∫ x,f (cubeRetraction k x) ∂(auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ))) =
      ∫ H,limitTestExpectation H ζ φ c d k f ∂μ := by
  have hm := hf.measurable.comp ((cubeRetraction_continuous k).measurable.comp
    (auxiliaryTrajectory_measurable ζ φ hζ hφ c d k))
  obtain ⟨M,_hM,hb⟩ := compact_test_bound f hf
  have hi : Integrable (fun p => f (cubeRetraction k (auxiliaryTrajectory ζ φ c d k p))) (μ.prod noiseLaw) :=
    Integrable.of_bound hm.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hb _)
  change (∫ x,f (cubeRetraction k x) ∂(μ.prod noiseLaw).map (auxiliaryTrajectory ζ φ c d k)) = _
  have he := integral_map (auxiliaryTrajectory_measurable ζ φ hζ hφ c d k).aemeasurable
      (show AEStronglyMeasurable (fun x => f (cubeRetraction k x)) ((μ.prod noiseLaw).map (auxiliaryTrajectory ζ φ c d k)) from
        (hf.measurable.comp (cubeRetraction_continuous k).measurable).aestronglyMeasurable)
  rw [he,integral_prod _ hi]
  rfl

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

theorem native_root_trajectory_measurable {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω)
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ) :
    Measurable (fun ω (r : Fin (k+1)) => S.R ζ φ c d m r ω (S.I m ω)) := by
  apply measurable_pi_lambda
  intro r
  exact measurable_countable_choice (fun i ω => S.R ζ φ c d m r ω i)
    (native_R_measurable P S 𝓖 ζ φ c d hS m r) (S.I m)
    ((hS.measurable_I m).mono (hS.le m) le_rfl)

noncomputable def nativeTrajectoryCondProbability {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] (P : Measure Ω) [IsFiniteMeasure P] (S : GraphSeq Ω A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (m k : ℕ) (ω : Ω) :
    ProbabilityMeasure (Fin (k+1) → ℝ) :=
  ⟨trajCondLaw P S ζ φ c d m k ω,by unfold trajCondLaw; infer_instance⟩

theorem native_trajectory_cond_support {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ) :
    ∀ᵐ ω ∂P,∀ᵐ x ∂trajCondLaw P S ζ φ c d m k ω,∀ r,x r∈Icc (-1:ℝ) 1 := by
  apply conditional_law_support P (S.attrs m)
    (fun ω (r : Fin (k+1)) => S.R ζ φ c d m r ω (S.I m ω))
    ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl).aemeasurable
    (native_root_trajectory_measurable P S 𝓖 ζ φ c d hS m k).aemeasurable
    (fun x => ∀ r,x r∈Icc (-1:ℝ) 1)
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun r => isClosed_Icc.measurableSet.preimage (measurable_pi_apply r)
  · exact Filter.Eventually.of_forall fun ω r => native_opinion_mem P S 𝓖 ζ φ c d hS m r ω _

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

 theorem uniform_pair_measure {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [MeasurableSpace I] [MeasurableSpace J] [MeasurableSingletonClass I] [MeasurableSingletonClass J] :
    (PMF.uniformOfFintype I).toMeasure.prod (PMF.uniformOfFintype J).toMeasure =
      (PMF.uniformOfFintype (I × J)).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [show ({p} : Set (I × J)) = {p.1} ×ˢ {p.2} by ext q; simp]
  rw [Measure.prod_prod]
  rw [← show ({p} : Set (I × J)) = {p.1} ×ˢ {p.2} by ext q; simp]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))).symm

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_pair_index_law (m : ℕ) :
    HasLaw (fun ω => (S.I m ω, S.J m ω))
      (PMF.uniformOfFintype (Fin (m+1) × Fin (m+1))).toMeasure P := by
  have hij : IndepFun (S.I m) (S.J m) P := (hS.indep_I m).comp measurable_id measurable_fst
  simpa only [uniform_pair_measure] using hij.hasLaw_prod (hS.I_unif m) (hS.J_unif m)

theorem native_pair_index_indep_graph_noise (m : ℕ) :
    IndepFun (fun ω => (S.I m ω, S.J m ω))
      (fun ω => (S.graphData m ω, fun p => S.unif m p ω)) P := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have hgl : HasLaw (S.graphData m) (P.map (S.graphData m)) P := ⟨hg.aemeasurable, rfl⟩
  have hjg := (hS.indep_J m).hasLaw_prod (hS.J_unif m) hgl
  have hijg := (hS.indep_I m).hasLaw_prod (hS.I_unif m) hjg
  have hinv : HasLaw (MeasurableEquiv.prodAssoc.symm :
      Fin (m+1) × (Fin (m+1) × NativeGraphData A m) →
      (Fin (m+1) × Fin (m+1)) × NativeGraphData A m)
      (((uniformVertex m).prod (uniformVertex m)).prod (P.map (S.graphData m)))
      ((uniformVertex m).prod ((uniformVertex m).prod (P.map (S.graphData m)))) := by
    refine ⟨MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable, ?_⟩
    rw [← Measure.prodAssoc_prod, MeasurableEquiv.map_symm_map]
  have hpairg := hinv.comp hijg
  have htotal := native_struct_noise_jointLaw P S 𝓖 ζ φ c d hS m
    (fun ω => ((S.I m ω, S.J m ω), S.graphData m ω))
    (((hS.measurable_I m).prodMk (hS.measurable_J m)).prodMk (hS.measurable_graph m)) _ hpairg
  have hassoc : HasLaw (MeasurableEquiv.prodAssoc :
      ((Fin (m+1) × Fin (m+1)) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ) →
      (Fin (m+1) × Fin (m+1)) × (NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ)))
      (((uniformVertex m).prod (uniformVertex m)).prod
        ((P.map (S.graphData m)).prod (finiteVertexNoiseLaw m)))
      ((((uniformVertex m).prod (uniformVertex m)).prod (P.map (S.graphData m))).prod
        (finiteVertexNoiseLaw m)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable.aemeasurable, Measure.prodAssoc_prod⟩
  have hgn := native_struct_noise_jointLaw P S 𝓖 ζ φ c d hS m
    (S.graphData m) (hS.measurable_graph m) _ hgl
  apply (indepFun_iff_hasLaw_prodMk_prod (native_pair_index_law P S 𝓖 ζ φ c d hS m) hgn).2
  have hh := hassoc.comp htotal
  change HasLaw (fun ω => ((S.I m ω, S.J m ω), (S.graphData m ω, fun p => S.unif m p ω))) _ P at hh
  simpa only [uniformVertex, uniform_pair_measure] using hh

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem uniform_index_integral {Ω I : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (P : Measure Ω) [IsFiniteMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (J : Ω → I) (hJ : Measurable[mΩ] J)
    (hindep : Indep (MeasurableSpace.comap J inferInstance) m P)
    (hLaw : HasLaw J (PMF.uniformOfFintype I).toMeasure P)
    (g : I → Ω → ℝ) (hgm : ∀ i, StronglyMeasurable[m] (g i))
    (hgi : ∀ i, Integrable (g i) P) :
    (∫ ω, g (J ω) ω ∂P) = ∫ ω, (Fintype.card I : ℝ)⁻¹ * ∑ i, g i ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  rw [← integral_condExp hm]
  exact integral_congr_ae (uniform_index_condExp P m hm J hJ hindep hLaw g hgm hgi)

theorem native_empirical_moment_identities {Ω A : Type*} [mΩ : MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ)
    (K : Fin (m+1) → NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) → ℝ)
    (hK : ∀ i, Measurable (K i)) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i z, |K i z| ≤ B) :
    let D := fun ω => (S.graphData m ω, fun p => S.unif m p ω)
    let F := fun ω => (Fintype.card (Fin (m+1)) : ℝ)⁻¹ * ∑ i, K i (D ω)
    (∫ ω, F ω ∂P) = (∫ ω, K (S.I m ω) (D ω) ∂P) ∧
    (∫ ω, F ω ^ 2 ∂P) = (∫ ω, K (S.I m ω) (D ω) * K (S.J m ω) (D ω) ∂P) := by
  dsimp only
  let D := fun ω => (S.graphData m ω, fun p => S.unif m p ω)
  let M : MeasurableSpace Ω := MeasurableSpace.comap D inferInstance
  let : MeasurableSpace Ω := mΩ
  have hD : Measurable D := ((hS.measurable_graph m).mono (hS.le m) le_rfl).prodMk
    (measurable_pi_lambda _ (hS.measurable_unif m))
  have hDM : Measurable[M] D := Measurable.of_comap_le le_rfl
  have hgm : ∀ i, StronglyMeasurable[M] (fun ω => K i (D ω)) :=
    fun i => ((hK i).comp hDM).stronglyMeasurable
  have hgi : ∀ i, Integrable (fun ω => K i (D ω)) P := by
    intro i
    exact Integrable.of_bound ((hK i).comp hD).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb i (D ω))
  have hI := (hS.measurable_I m).mono (hS.le m) le_rfl
  have hJ := (hS.measurable_J m).mono (hS.le m) le_rfl
  constructor
  · exact (uniform_index_integral P M hD.comap_le (S.I m) hI
      (native_index_indep_graph_noise P S 𝓖 ζ φ c d hS m) (hS.I_unif m)
      (fun i ω => K i (D ω)) hgm hgi).symm
  · have hpm : ∀ p : Fin (m+1) × Fin (m+1),
        StronglyMeasurable[M] (fun ω => K p.1 (D ω)*K p.2 (D ω)) :=
      fun p => (hgm p.1).mul (hgm p.2)
    have hpi : ∀ p : Fin (m+1) × Fin (m+1),
        Integrable (fun ω => K p.1 (D ω)*K p.2 (D ω)) P := by
      intro p
      apply Integrable.of_bound (((hK p.1).comp hD).mul ((hK p.2).comp hD)).aestronglyMeasurable (B*B)
      apply Filter.Eventually.of_forall
      intro ω
      simp only [Pi.mul_apply, Function.comp_def]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hB
    have hp := uniform_index_integral P M hD.comap_le (fun ω => (S.I m ω, S.J m ω))
      (hI.prodMk hJ) (native_pair_index_indep_graph_noise P S 𝓖 ζ φ c d hS m)
      (native_pair_index_law P S 𝓖 ζ φ c d hS m)
      (fun p ω => K p.1 (D ω)*K p.2 (D ω)) hpm hpi
    rw [hp]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem native_trajectory_empirical_moment_identities {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    let T := fun ω i => f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i))
    let F := fun ω => (1/((m:ℝ)+1))*∑ i, T ω i
    (∫ ω, F ω ∂P) = (∫ ω, T ω (S.I m ω) ∂P) ∧
    (∫ ω, F ω ^ 2 ∂P) = (∫ ω, T ω (S.I m ω)*T ω (S.J m ω) ∂P) := by
  let K : Fin (m+1) → NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) → ℝ :=
    fun i p => f (cubeRetraction k (nativeKernelTrajectory ζ φ c d p.1 p.2 k i))
  have hK : ∀ i, Measurable (K i) := fun i => hf.measurable.comp
    ((cubeRetraction_continuous k).measurable.comp
      (nativeKernelTrajectory_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i))
  obtain ⟨B, hB, hb⟩ := compact_test_bound f hf
  have h := native_empirical_moment_identities P S 𝓖 ζ φ c d hS m K hK B hB
    (fun i p => hb (cubeRetraction k (nativeKernelTrajectory ζ φ c d p.1 p.2 k i)))
  have he : ∀ i ω, K i (S.graphData m ω, fun p => S.unif m p ω) =
      f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i)) := by
    intro i ω
    apply congrArg f
    apply congrArg (cubeRetraction k)
    funext r
    exact nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m r ω i
  dsimp only at h ⊢
  simpa only [he, Fintype.card_fin, Nat.cast_add, Nat.cast_one, one_div] using h

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Finset Filter Topology

theorem delta_sum {V I : Type*} (G : WDigraph V) (c d : ℝ)
    (s : Finset I) (f : I → V → ℝ) :
    Δ G c d (fun i => ∑ j ∈ s, f j i) = fun i => ∑ j ∈ s, Δ G c d (f j) i := by
  funext i
  simp only [Δ, mul_sum, sum_add_distrib]
  rw [sum_comm]

theorem stationary_summable {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (W : ℕ → V → ℝ) (hW : ∀ k i, |W k i| ≤ G.budget c d i) (i : V) :
    Summable (fun r => (Δ G c d)^[r] (W r) i) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (by linarith : 0 ≤ 1-d) (by linarith))
  intro r
  simpa only [Real.norm_eq_abs, mul_one] using
    delta_iterate_abs_le G hG hc hcd hd1 (by norm_num : (0:ℝ) ≤ 1)
      (W r) (fun j => (hW r j).trans (budget_le_one G hG hcd j)) r i

theorem stationary_partial_abs_le_one {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hcd : c + d ≤ 1) :
    ∀ k (W : ℕ → V → ℝ), (∀ t i, |W t i| ≤ G.budget c d i) →
      ∀ i, |∑ r ∈ range k, (Δ G c d)^[r] (W r) i| ≤ 1 := by
  intro k
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro W hW i
    have ht := ih (fun r => W (r+1)) (fun r j => hW (r+1) j)
    have hδ := delta_abs_local G hG hcd
      (fun j => ∑ r ∈ range k, (Δ G c d)^[r] (W (r+1)) j) ht i
    rw [delta_sum] at hδ
    have hw := hW 0 i
    unfold WDigraph.budget at hw
    rw [sum_range_succ']
    simp only [Function.iterate_zero, id_eq]
    have heq : (∑ r ∈ range k, (Δ G c d)^[r+1] (W (r+1)) i) =
        ∑ r ∈ range k, Δ G c d ((Δ G c d)^[r] (W (r+1))) i := by
      apply sum_congr rfl
      intro r _
      rw [Function.iterate_succ_apply']
    rw [heq]
    have hab := abs_add_le (∑ r ∈ range k, Δ G c d ((Δ G c d)^[r] (W (r+1))) i) (W 0 i)
    linarith

theorem stationary_abs_le_one {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (W : ℕ → V → ℝ) (hW : ∀ k i, |W k i| ≤ G.budget c d i) (i : V) :
    |stationary G c d W i| ≤ 1 := by
  have hs := stationary_summable G hG hc hcd hd hd1 W hW i
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat.abs
    (Filter.Eventually.of_forall fun k => stationary_partial_abs_le_one G hG hcd k W hW i)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Finset

theorem stationary_tail_bound {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (W : ℕ → V → ℝ) (hW : ∀ k i, |W k i| ≤ G.budget c d i) (k : ℕ) (i : V) :
    |stationary G c d W i - ∑ r ∈ range k, (Δ G c d)^[r] (W r) i| ≤ (1-d)^k / d := by
  have hg0 : 0 ≤ 1-d := by linarith
  have hg1 : 1-d < 1 := by linarith
  have hs := stationary_summable G hG hc hcd hd hd1 W hW i
  have he := hs.sum_add_tsum_nat_add k
  have hb : ∀ r, ‖(Δ G c d)^[r+k] (W (r+k)) i‖ ≤ (1-d)^r * (1-d)^k := by
    intro r
    simpa only [Real.norm_eq_abs, mul_one, pow_add] using
      delta_iterate_abs_le G hG hc hcd hd1 (by norm_num : (0:ℝ) ≤ 1)
        (W (r+k)) (fun j => (hW (r+k) j).trans (budget_le_one G hG hcd j)) (r+k) i
  have hgeo : Summable (fun r : ℕ => (1-d)^r * (1-d)^k) :=
    (summable_geometric_of_lt_one hg0 hg1).mul_right _
  have hn : Summable (fun r => ‖(Δ G c d)^[r+k] (W (r+k)) i‖) :=
    hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hnorm := norm_tsum_le_tsum_norm hn
  have hsum := hn.tsum_le_tsum hb hgeo
  have hv : (∑' r : ℕ, (1-d)^r * (1-d)^k) = (1-d)^k / d := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hg0 hg1]
    have hx : 1-(1-d) = d := by ring
    rw [hx]
    ring
  have hident : stationary G c d W i - ∑ r ∈ range k, (Δ G c d)^[r] (W r) i =
      ∑' r : ℕ, (Δ G c d)^[r+k] (W (r+k)) i := by
    unfold stationary
    linarith
  rw [hident]
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans (hsum.trans_eq hv)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open Finset

theorem delta_add_functions {V : Type*} (G : WDigraph V) (c d : ℝ) (f g : V → ℝ) :
    Δ G c d (f + g) = Δ G c d f + Δ G c d g := by
  funext i
  simp only [Δ, Pi.add_apply, mul_add, sum_add_distrib]
  ring

theorem opinion_expansion {V : Type*} (G : WDigraph V) (c d : ℝ)
    (R0 : V → ℝ) (W : ℕ → V → ℝ) (k : ℕ) (i : V) :
    opinion G c d R0 W k i = (Δ G c d)^[k] R0 i +
      ∑ r ∈ range k, (Δ G c d)^[r] (W (k - 1 - r)) i := by
  induction k generalizing i with
  | zero => simp [opinion]
  | succ k ih =>
    have heq : opinion G c d R0 W k = (Δ G c d)^[k] R0 +
        (fun j => ∑ r ∈ range k, (Δ G c d)^[r] (W (k - 1 - r)) j) := by
      funext j
      exact ih j
    rw [opinion, heq, delta_add_functions, delta_sum]
    rw [sum_range_succ']
    simp only [Pi.add_apply, Nat.add_sub_cancel, Function.iterate_zero, id_eq,
      Function.iterate_succ_apply']
    have he : (∑ r ∈ range k, Δ G c d ((Δ G c d)^[r] (W (k - 1 - r))) i) =
        ∑ r ∈ range k, Δ G c d ((Δ G c d)^[r] (W (k - (r + 1)))) i := by
      apply sum_congr rfl
      intro r _
      congr 3; omega
    rw [he]
    simp only [Nat.sub_zero, add_assoc]

theorem reversed_opinion_expansion {V : Type*} (G : WDigraph V) (c d : ℝ)
    (R0 : V → ℝ) (W : ℕ → V → ℝ) (k : ℕ) (i : V) :
    opinion G c d R0 (fun t => W (k - 1 - t)) k i = (Δ G c d)^[k] R0 i +
      ∑ r ∈ range k, (Δ G c d)^[r] (W r) i := by
  rw [opinion_expansion]
  congr 1
  apply sum_congr rfl
  intro r hr
  have he : k - 1 - (k - 1 - r) = r := by have := mem_range.mp hr; omega
  rw [he]

theorem reversed_endpoint_stationary_bound {V : Type*} (G : WDigraph V) {c d : ℝ}
    (hG : G.Valid c) (hc : 0 ≤ c) (hcd : c + d ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (R0 : V → ℝ) (hR0 : ∀ i, |R0 i| ≤ 1)
    (W : ℕ → V → ℝ) (hW : ∀ k i, |W k i| ≤ G.budget c d i) (k : ℕ) (i : V) :
    |opinion G c d R0 (fun t => W (k - 1 - t)) k i - stationary G c d W i| ≤
      (1-d)^k * (1 + 1/d) := by
  rw [reversed_opinion_expansion]
  have hi := delta_iterate_abs_le G hG hc hcd hd1 (by norm_num : (0:ℝ) ≤ 1) R0 hR0 k i
  have ht := stationary_tail_bound G hG hc hcd hd hd1 W hW k i
  have ha := abs_add_le ((Δ G c d)^[k] R0 i)
    ((∑ r ∈ range k, (Δ G c d)^[r] (W r) i) - stationary G c d W i)
  rw [abs_sub_comm] at ht
  have he : (1-d)^k * (1+1/d) = (1-d)^k + (1-d)^k / d := by ring
  rw [he]
  simp only [mul_one] at hi
  simpa only [add_sub_assoc] using ha.trans (add_le_add hi ht)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

def reverseTime (k t : ℕ) : ℕ := if t < k then k - 1 - t else t

theorem reverseTime_involutive (k : ℕ) : Function.Involutive (reverseTime k) := by
  intro t
  unfold reverseTime
  split_ifs <;> omega

def reverseTimeEquiv (k : ℕ) : ℕ ≃ ℕ := ⟨reverseTime k, reverseTime k, reverseTime_involutive k, reverseTime_involutive k⟩

def reverseNoiseIndex (m k : ℕ) : (Option ℕ × Fin (m + 1)) ≃ (Option ℕ × Fin (m + 1)) :=
  Equiv.prodCongr (Equiv.optionCongr (reverseTimeEquiv k)) (Equiv.refl _)

@[simp] theorem reverseNoiseIndex_none (m k : ℕ) (i : Fin (m + 1)) :
    reverseNoiseIndex m k (none, i) = (none, i) := rfl

@[simp] theorem reverseNoiseIndex_some (m k t : ℕ) (i : Fin (m + 1)) :
    reverseNoiseIndex m k (some t, i) = (some (reverseTime k t), i) := rfl

theorem reverseTime_lt (k t : ℕ) (ht : t < k) : reverseTime k t = k - 1 - t := by
  simp [reverseTime, ht]

def reverseNoiseArray (m k : ℕ) (u : Option ℕ × Fin (m + 1) → ℝ) :
    Option ℕ × Fin (m + 1) → ℝ := fun p => u (reverseNoiseIndex m k p)

theorem measurable_reverseNoiseArray (m k : ℕ) : Measurable (reverseNoiseArray m k) :=
  measurable_pi_lambda _ (fun p => measurable_pi_apply (reverseNoiseIndex m k p))

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω)
variable (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_reversed_noise_hasLaw (m k : ℕ) :
    HasLaw (fun ω p => S.unif m (reverseNoiseIndex m k p) ω) (finiteVertexNoiseLaw m) P := by
  exact iIndepFun.hasLaw_infinitePi (fun p => hS.unif_law m (reverseNoiseIndex m k p))
    (iIndepFun.precomp (reverseNoiseIndex m k).injective (hS.unif_iIndep m))
    (measurable_pi_lambda _ (fun p => hS.measurable_unif m (reverseNoiseIndex m k p))).aemeasurable

theorem native_reversed_noise_indep_struct {X : Type*} [MeasurableSpace X]
    (m k : ℕ) (T : Ω → X) (hT : Measurable[𝓖 m] T) :
    IndepFun (fun ω p => S.unif m (reverseNoiseIndex m k p) ω) T P := by
  exact (native_noise_indep_struct_function P S 𝓖 ζ φ c d hS m T hT).comp
    (measurable_reverseNoiseArray m k) measurable_id

theorem native_struct_reversed_noise_jointLaw [IsProbabilityMeasure P]
    {X : Type*} [MeasurableSpace X] (m k : ℕ) (T : Ω → X)
    (hT : Measurable[𝓖 m] T) (ν : Measure X) (hLaw : HasLaw T ν P) :
    HasLaw (fun ω => (T ω, fun p => S.unif m (reverseNoiseIndex m k p) ω))
      (ν.prod (finiteVertexNoiseLaw m)) P := by
  exact (native_reversed_noise_indep_struct P S 𝓖 ζ φ c d hS m k T hT).symm.hasLaw_prod
    hLaw (native_reversed_noise_hasLaw P S 𝓖 ζ φ c d hS m k)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_reversal_observable_map_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (m k : ℕ) (T : Ω → X) (hT : Measurable[𝓖 m] T)
    (F : X × (Option ℕ × Fin (m+1) → ℝ) → Y) (hF : Measurable F) :
    P.map (fun ω => F (T ω, fun p => S.unif m (reverseNoiseIndex m k p) ω)) =
      P.map (fun ω => F (T ω, fun p => S.unif m p ω)) := by
  have hTa : Measurable T := hT.mono (hS.le m) le_rfl
  have hTl : HasLaw T (P.map T) P := ⟨hTa.aemeasurable, rfl⟩
  have hrev := native_struct_reversed_noise_jointLaw P S 𝓖 ζ φ c d hS m k T hT _ hTl
  have horig := native_struct_noise_jointLaw P S 𝓖 ζ φ c d hS m T hT _ hTl
  have hFl : HasLaw F (((P.map T).prod (finiteVertexNoiseLaw m)).map F)
      ((P.map T).prod (finiteVertexNoiseLaw m)) := ⟨hF.aemeasurable, rfl⟩
  exact (hFl.comp hrev).map_eq.trans (hFl.comp horig).map_eq.symm

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω)
variable (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem nativeKernelOpinion_reversed (m k : ℕ) (ω : Ω) (i : Fin (m+1)) :
    nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i =
    opinion (S.G m ω) c d (S.R0 φ m ω)
      (fun t j => S.W ζ m (k - 1 - t) j ω) k i := by
  change clippedOpinion (S.G m ω) c d (S.R0 φ m ω)
    (fun t j => S.W ζ m (reverseTime k t) j ω) k i = _
  calc
    _ = clippedOpinion (S.G m ω) c d (S.R0 φ m ω)
        (fun t j => S.W ζ m (k - 1 - t) j ω) k i := by
      apply clippedOpinion_locality
      · intro j _; rfl
      · intro t ht j _
        rw [reverseTime_lt k t ht]
    _ = _ := congrFun (clippedOpinion_eq (S.G m ω) (hS.valid m ω) hS.cd_le_one _ _
      (fun j => abs_le.mpr (hS.φ_mem _ _)) (fun t j => hS.signal_bound m (k-1-t) j ω) k) i

theorem native_reversed_endpoint_stationary_bound (m k : ℕ) (ω : Ω) (i : Fin (m+1)) :
    |nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i - S.Rstat ζ c d m ω i| ≤
      (1-d)^k * (1+1/d) := by
  rw [nativeKernelOpinion_reversed P S 𝓖 ζ φ c d hS]
  exact reversed_endpoint_stationary_bound (S.G m ω) (hS.valid m ω) hS.c_nonneg
    hS.cd_le_one hS.d_pos hS.d_le_one (S.R0 φ m ω)
    (fun j => abs_le.mpr (hS.φ_mem _ _)) (fun t j => S.W ζ m t j ω)
    (fun t j => hS.signal_bound m t j ω) k i

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset Filter Topology

theorem delta_iterate_measurable {Ω V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
    (G : Ω → WDigraph V) (c d : ℝ) (f : Ω → V → ℝ)
    (hdeg : ∀ i, Measurable (fun ω => (G ω).deg i))
    (hnbr : ∀ i r, Measurable (fun ω => (G ω).nbr i r))
    (hwt : ∀ i r, Measurable (fun ω => (G ω).wt i r))
    (hf : ∀ i, Measurable (fun ω => f ω i)) :
    ∀ k i, Measurable (fun ω => (Δ (G ω) c d)^[k] (f ω) i) := by
  intro k
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro i
    simp only [Function.iterate_succ_apply']
    change Measurable (fun ω => (∑ r ∈ range ((G ω).deg i), (G ω).wt i r *
      (Δ (G ω) c d)^[k] (f ω) ((G ω).nbr i r)) + (1-c-d) * (Δ (G ω) c d)^[k] (f ω) i)
    apply Measurable.add
    · apply measurable_variable_sum _ _ _ (hdeg i)
      intro r
      exact (hwt i r).mul (measurable_countable_choice _ ih _ (hnbr i r))
    · exact measurable_const.mul (ih i)

theorem native_Rstat_measurable {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω)
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ) (i : Fin (m+1)) :
    Measurable (fun ω => S.Rstat ζ c d m ω i) := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have hterm : ∀ r, Measurable (fun ω =>
      (Δ (S.G m ω) c d)^[r] (fun j => S.W ζ m r j ω) i) := by
    intro r
    apply delta_iterate_measurable
    · intro j; exact hg.fst.eval
    · intro j t; exact hg.snd.fst.eval.eval
    · intro j t; exact hg.snd.snd.fst.eval.eval
    · intro j
      exact hS.measurable_ζ.comp ((native_mark_measurable P S 𝓖 ζ φ c d hS m j).prodMk
        (hS.measurable_unif m (some r,j)))
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => ∑ r ∈ range n, (Δ (S.G m ω) c d)^[r] (fun j => S.W ζ m r j ω) i)
    (fun n => Finset.measurable_sum _ (fun r _ => hterm r))
  apply tendsto_pi_nhds.2
  intro ω
  exact (stationary_summable (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
    hS.d_le_one (fun r j => S.W ζ m r j ω) (fun r j => hS.signal_bound m r j ω) i).hasSum.tendsto_sum_nat

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_root_reversed_endpoint_map (m k : ℕ) :
    P.map (fun ω => nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k (S.I m ω)) =
    P.map (fun ω => S.R ζ φ c d m k ω (S.I m ω)) := by
  let F : (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ) → ℝ :=
    fun p => nativeKernelOpinion ζ φ c d p.1.2 p.2 k p.1.1
  have hF : Measurable F := by
    apply measurable_countable_choice
      (fun i (p : (Fin (m+1) × NativeGraphData A m) × (Option ℕ × Fin (m+1) → ℝ)) => nativeKernelOpinion ζ φ c d p.1.2 p.2 k i) _ (fun p => p.1.1)
      (by fun_prop)
    intro i
    exact (nativeKernelOpinion_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i).comp
      (measurable_fst.snd.prodMk measurable_snd)
  have he := native_reversal_observable_map_eq P S 𝓖 ζ φ c d hS m k
    (fun ω => (S.I m ω, S.graphData m ω))
    ((hS.measurable_I m).prodMk (hS.measurable_graph m)) F hF
  have ho : (fun ω => F ((S.I m ω, S.graphData m ω), fun p => S.unif m p ω)) =
      (fun ω => S.R ζ φ c d m k ω (S.I m ω)) := by
    funext ω
    exact nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m k ω (S.I m ω)
  rw [ho] at he
  exact he

omit [IsProbabilityMeasure P] in
theorem native_root_R_measurable (m k : ℕ) :
    Measurable (fun ω => S.R ζ φ c d m k ω (S.I m ω)) :=
  measurable_countable_choice _ (native_R_measurable P S 𝓖 ζ φ c d hS m k) _
    ((hS.measurable_I m).mono (hS.le m) le_rfl)

omit [IsProbabilityMeasure P] in
theorem native_root_Rstat_measurable (m : ℕ) :
    Measurable (fun ω => S.Rstat ζ c d m ω (S.I m ω)) :=
  measurable_countable_choice _ (native_Rstat_measurable P S 𝓖 ζ φ c d hS m) _
    ((hS.measurable_I m).mono (hS.le m) le_rfl)

omit [IsProbabilityMeasure P] in
theorem native_root_reversed_measurable (m k : ℕ) :
    Measurable (fun ω => nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k (S.I m ω)) := by
  have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
  have hu : Measurable (fun ω p => S.unif m (reverseNoiseIndex m k p) ω) :=
    measurable_pi_lambda _ (fun p => hS.measurable_unif m (reverseNoiseIndex m k p))
  apply measurable_countable_choice
    (fun i ω => nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i) _ (S.I m)
    ((hS.measurable_I m).mono (hS.le m) le_rfl)
  intro i
  exact (nativeKernelOpinion_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i).comp
    (hg.prodMk hu)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem compact_coupling_limit {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ ν : ℕ → ProbabilityMeasure X) (μlim νlim : ProbabilityMeasure X)
    (hμ : Tendsto μ atTop (𝓝 μlim)) (hν : Tendsto ν atTop (𝓝 νlim))
    (π : ℕ → ProbabilityMeasure (X × X))
    (hπ : ∀ n, IsCoupling (π n : Measure (X × X)) (μ n : Measure X) (ν n : Measure X))
    (g : C(X × X, ℝ)) (B : ℕ → ℝ) (b : ℝ) (hB : Tendsto B atTop (𝓝 b))
    (hcost : ∀ n, (∫ z, g z ∂(π n : Measure (X × X))) ≤ B n) :
    ∃ πlim : ProbabilityMeasure (X × X),
      IsCoupling (πlim : Measure (X × X)) (μlim : Measure X) (νlim : Measure X) ∧
      (∫ z, g z ∂(πlim : Measure (X × X))) ≤ b := by
  obtain ⟨πlim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq π
  have hfst : Tendsto (fun n => (π (φ n)).map measurable_fst.aemeasurable)
      atTop (𝓝 (πlim.map measurable_fst.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (π ∘ φ) πlim hlim continuous_fst
  have hsnd : Tendsto (fun n => (π (φ n)).map measurable_snd.aemeasurable)
      atTop (𝓝 (πlim.map measurable_snd.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (π ∘ φ) πlim hlim continuous_snd
  have hfm : (fun n => (π (φ n)).map measurable_fst.aemeasurable) = μ ∘ φ := by
    funext n
    apply Subtype.ext
    exact (hπ (φ n)).2.1
  have hsm : (fun n => (π (φ n)).map measurable_snd.aemeasurable) = ν ∘ φ := by
    funext n
    apply Subtype.ext
    exact (hπ (φ n)).2.2
  have hflim : πlim.map measurable_fst.aemeasurable = μlim := by
    apply tendsto_nhds_unique hfst
    rw [hfm]
    exact hμ.comp hφ.tendsto_atTop
  have hslim : πlim.map measurable_snd.aemeasurable = νlim := by
    apply tendsto_nhds_unique hsnd
    rw [hsm]
    exact hν.comp hφ.tendsto_atTop
  refine ⟨πlim, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · exact congrArg (fun m : ProbabilityMeasure X => (m : Measure X)) hflim
  · exact congrArg (fun m : ProbabilityMeasure X => (m : Measure X)) hslim
  · have hi := (ProbabilityMeasure.continuous_integral_continuousMap g).tendsto πlim |>.comp hlim
    exact le_of_tendsto_of_tendsto hi (hB.comp hφ.tendsto_atTop)
      (Filter.Eventually.of_forall fun n => hcost (φ n))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

abbrev OpinionInterval := Icc (-1 : ℝ) 1

noncomputable def scalarOpinionClamp (x : ℝ) : OpinionInterval :=
  ⟨clip (-1) 1 x, clip_mem (by norm_num) x⟩

theorem scalarOpinionClamp_continuous : Continuous scalarOpinionClamp :=
  (continuous_clip (-1) 1).subtype_mk _

theorem scalarOpinionClamp_eq (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    (scalarOpinionClamp x : ℝ) = x := clip_eq hx

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)

noncomputable def nativeCompactEndpointLaw (m k : ℕ) : ProbabilityMeasure OpinionInterval :=
  ⟨P.map (fun ω => scalarOpinionClamp (S.R ζ φ c d m k ω (S.I m ω))),
    Measure.isProbabilityMeasure_map (scalarOpinionClamp_continuous.measurable.comp
      (native_root_R_measurable P S 𝓖 ζ φ c d hS m k)).aemeasurable⟩

noncomputable def nativeCompactStationaryLaw (m : ℕ) : ProbabilityMeasure OpinionInterval :=
  ⟨P.map (fun ω => scalarOpinionClamp (S.Rstat ζ c d m ω (S.I m ω))),
    Measure.isProbabilityMeasure_map (scalarOpinionClamp_continuous.measurable.comp
      (native_root_Rstat_measurable P S 𝓖 ζ φ c d hS m)).aemeasurable⟩

theorem native_endpoint_stationary_compact_coupling (m k : ℕ) :
    ∃ π : ProbabilityMeasure (OpinionInterval × OpinionInterval),
      IsCoupling (π : Measure (OpinionInterval × OpinionInterval))
        (nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k : Measure OpinionInterval)
        (nativeCompactStationaryLaw P S 𝓖 ζ φ c d hS m : Measure OpinionInterval) ∧
      (∫ z, dist z.1 z.2 ∂(π : Measure (OpinionInterval × OpinionInterval))) ≤
        (1-d)^k * (1+1/d) := by
  let X : Ω → ℝ := fun ω => nativeKernelOpinion ζ φ c d (S.graphData m ω)
    (fun p => S.unif m (reverseNoiseIndex m k p) ω) k (S.I m ω)
  let Y : Ω → ℝ := fun ω => S.Rstat ζ c d m ω (S.I m ω)
  have hX : Measurable X := native_root_reversed_measurable P S 𝓖 ζ φ c d hS m k
  have hY : Measurable Y := native_root_Rstat_measurable P S 𝓖 ζ φ c d hS m
  let Z : Ω → OpinionInterval × OpinionInterval :=
    fun ω => (scalarOpinionClamp (X ω), scalarOpinionClamp (Y ω))
  have hZ : Measurable Z := (scalarOpinionClamp_continuous.measurable.comp hX).prodMk
    (scalarOpinionClamp_continuous.measurable.comp hY)
  let π : ProbabilityMeasure (OpinionInterval × OpinionInterval) :=
    ⟨P.map Z, Measure.isProbabilityMeasure_map hZ.aemeasurable⟩
  have hf : (π : Measure (OpinionInterval × OpinionInterval)).map Prod.fst =
      (nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k : Measure OpinionInterval) := by
    change (P.map Z).map Prod.fst = _
    rw [Measure.map_map measurable_fst hZ]
    change P.map (scalarOpinionClamp ∘ X) = _
    rw [← Measure.map_map scalarOpinionClamp_continuous.measurable hX,
      native_root_reversed_endpoint_map P S 𝓖 ζ φ c d hS m k,
      Measure.map_map scalarOpinionClamp_continuous.measurable
        (native_root_R_measurable P S 𝓖 ζ φ c d hS m k)]
    rfl
  have hs : (π : Measure (OpinionInterval × OpinionInterval)).map Prod.snd =
      (nativeCompactStationaryLaw P S 𝓖 ζ φ c d hS m : Measure OpinionInterval) := by
    change (P.map Z).map Prod.snd = _
    rw [Measure.map_map measurable_snd hZ]
    rfl
  refine ⟨π, ⟨inferInstance, hf, hs⟩, ?_⟩
  have hb : ∀ ω, dist (Z ω).1 (Z ω).2 ≤ (1-d)^k * (1+1/d) := by
    intro ω
    have hx : X ω ∈ Icc (-1:ℝ) 1 := nativeKernelOpinion_mem _ _ _ _ _ _ _ _
    have hy : Y ω ∈ Icc (-1:ℝ) 1 := abs_le.mp
      (stationary_abs_le_one (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
        hS.d_le_one (fun t j => S.W ζ m t j ω) (fun t j => hS.signal_bound m t j ω) (S.I m ω))
    change |(scalarOpinionClamp (X ω) : ℝ) - (scalarOpinionClamp (Y ω) : ℝ)| ≤ _
    rw [scalarOpinionClamp_eq _ hx, scalarOpinionClamp_eq _ hy]
    exact native_reversed_endpoint_stationary_bound P S 𝓖 ζ φ c d hS m k ω (S.I m ω)
  have hba : ∀ᵐ z ∂(π : Measure (OpinionInterval × OpinionInterval)),
      dist z.1 z.2 ≤ (1-d)^k * (1+1/d) := by
    exact (ae_map_iff hZ.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).2 (Filter.Eventually.of_forall hb)
  have hint : Integrable (fun z : OpinionInterval × OpinionInterval => dist z.1 z.2)
      (π : Measure (OpinionInterval × OpinionInterval)) :=
    continuous_dist.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ _z, (1-d)^k * (1+1/d) ∂(π : Measure (OpinionInterval × OpinionInterval)) :=
      integral_mono_ae hint (integrable_const _) hba
    _ = _ := by simp

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

theorem compact_test_linear_modulus {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, |f x-f y| ≤ η+C*dist x y := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu η hη
  refine ⟨2*(max M 0)/δ,by positivity,?_⟩
  intro x y
  by_cases hd : dist x y < δ
  · have hxy := hclose hd
    rw [Real.dist_eq] at hxy
    have hn : 0 ≤ (2*max M 0/δ)*dist x y := by positivity
    linarith
  · have hx0 : |f x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    have hy0 : |f y| ≤ M := by simpa only [Real.norm_eq_abs] using hM y (mem_univ y)
    have hx := hx0.trans (le_max_left M 0)
    have hy := hy0.trans (le_max_left M 0)
    have hab := abs_sub_le (f x) 0 (f y)
    have hrat : 2*max M 0 ≤ (2*max M 0/δ)*dist x y := by
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hd)
        (div_nonneg (by positivity : 0≤2*max M 0) hδ.le)
      rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at hm
    simp only [sub_zero,zero_sub,abs_neg] at hab
    linarith

theorem integral_test_modulus_bound {Ω X : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [PseudoMetricSpace X] (F G : Ω → X) (f : X → ℝ)
    {η C E : ℝ} (hC : 0≤C) (hF : Integrable (fun ω => f (F ω)) μ)
    (hG : Integrable (fun ω => f (G ω)) μ)
    (hD : Integrable (fun ω => dist (F ω) (G ω)) μ)
    (hmod : ∀ ω, |f (F ω)-f (G ω)| ≤ η+C*dist (F ω) (G ω))
    (hE : (∫ ω,dist (F ω) (G ω) ∂μ) ≤ E) :
    |(∫ ω,f (F ω) ∂μ)-(∫ ω,f (G ω) ∂μ)| ≤ η+C*E := by
  rw [← integral_sub hF hG]
  apply abs_integral_le_integral_abs.trans
  have hbound := integral_mono_ae (hF.sub hG).abs
    ((integrable_const η).add (hD.const_mul C)) (Filter.Eventually.of_forall hmod)
  have heq := integral_add (integrable_const η) (hD.const_mul C)
  simp only [Pi.add_apply] at hbound heq
  rw [heq,integral_const,integral_const_mul] at hbound
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hbound
  exact hbound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hC))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem empAvg_sub_abs_le {m : ℕ} (f : ℝ → ℝ) (x y : Fin (m+1) → ℝ) (B : ℝ)
    (h : ∀ i, |f (x i)-f (y i)| ≤ B) : |empAvg f x-empAvg f y| ≤ B := by
  have hden : (0:ℝ) < m+1 := by positivity
  unfold empAvg
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(m+1))]
  calc
    _ ≤ (1/((m:ℝ)+1)) * ∑ i : Fin (m+1), B :=
      mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => h i)) (by positivity)
    _ = B := by simp; field_simp

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_empirical_reversed_map (m k : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    P.map (fun ω => empAvg f (fun i => nativeKernelOpinion ζ φ c d (S.graphData m ω)
      (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i)) =
    P.map (fun ω => empAvg f (S.R ζ φ c d m k ω)) := by
  let F : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) → ℝ :=
    fun p => empAvg f (fun i => nativeKernelOpinion ζ φ c d p.1 p.2 k i)
  have hF : Measurable F := by
    apply measurable_const.mul
    exact Finset.measurable_sum _ (fun i _ => hf.comp
      (nativeKernelOpinion_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i))
  have he := native_reversal_observable_map_eq P S 𝓖 ζ φ c d hS m k
    (S.graphData m) (hS.measurable_graph m) F hF
  have ho : (fun ω => F (S.graphData m ω, fun p => S.unif m p ω)) =
      (fun ω => empAvg f (S.R ζ φ c d m k ω)) := by
    funext ω
    dsimp only [F]
    apply congrArg (empAvg f)
    funext i
    exact nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m k ω i
  rw [ho] at he
  exact he

omit [IsProbabilityMeasure P] in
theorem native_empirical_stationary_approximation (f : C(OpinionInterval, ℝ))
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m k ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω) -
        empAvg (fun x => f (scalarOpinionClamp x))
          (fun i => nativeKernelOpinion ζ φ c d (S.graphData m ω)
            (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i)| ≤
        η+C*((1-d)^k*(1+1/d)) := by
  obtain ⟨C, hC, hmod⟩ := compact_test_linear_modulus f.continuous hη
  refine ⟨C, hC, ?_⟩
  intro m k ω
  apply empAvg_sub_abs_le
  intro i
  have hs : S.Rstat ζ c d m ω i ∈ Icc (-1:ℝ) 1 := abs_le.mp
    (stationary_abs_le_one (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
      hS.d_le_one (fun t j => S.W ζ m t j ω) (fun t j => hS.signal_bound m t j ω) i)
  have hx := nativeKernelOpinion_mem ζ φ c d (S.graphData m ω)
    (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i
  have he := native_reversed_endpoint_stationary_bound P S 𝓖 ζ φ c d hS m k ω i
  rw [abs_sub_comm] at he
  have hd : dist (scalarOpinionClamp (S.Rstat ζ c d m ω i))
      (scalarOpinionClamp (nativeKernelOpinion ζ φ c d (S.graphData m ω)
        (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i)) ≤ (1-d)^k*(1+1/d) := by
    change |(scalarOpinionClamp _ : ℝ)-(scalarOpinionClamp _ : ℝ)| ≤ _
    rw [scalarOpinionClamp_eq _ hs, scalarOpinionClamp_eq _ hx]
    exact he
  exact (hmod _ _).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hC))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

noncomputable def nativeTrajectoryEmpirical {Ω A : Type*} (S : GraphSeq Ω A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (f : FiniteCube k → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (1/((m:ℝ)+1))*∑ i, f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i))

theorem nativeTrajectoryEmpirical_bound {Ω A : Type*} (S : GraphSeq Ω A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (f : FiniteCube k → ℝ)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B) (m : ℕ) (ω : Ω) :
    |nativeTrajectoryEmpirical S ζ φ c d k f m ω| ≤ B := by
  have hh := empAvg_sub_abs_le (m := m) id
    (fun i => f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i)))
    (fun _ => 0) B (fun i => by simpa using hb (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω i)))
  simpa [empAvg, nativeTrajectoryEmpirical] using hh

theorem nativeTrajectoryEmpirical_measurable {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω)
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) (m : ℕ) :
    Measurable (nativeTrajectoryEmpirical S ζ φ c d k f m) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact hf.measurable.comp ((cubeRetraction_continuous k).measurable.comp
    (measurable_pi_lambda _ (fun r => native_R_measurable P S 𝓖 ζ φ c d hS m r i)))

theorem nativeTrajectoryEmpirical_integrable {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsFiniteMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) (m : ℕ) :
    Integrable (nativeTrajectoryEmpirical S ζ φ c d k f m) P ∧
      Integrable (fun ω => (nativeTrajectoryEmpirical S ζ φ c d k f m ω)^2) P := by
  obtain ⟨B, hB, hb⟩ := compact_test_bound f hf
  have hm := nativeTrajectoryEmpirical_measurable P S 𝓖 ζ φ c d hS k f hf m
  have hbound := nativeTrajectoryEmpirical_bound S ζ φ c d k f B hb m
  constructor
  · exact Integrable.of_bound hm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  · apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (B^2)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) 2

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Finset

theorem matched_kernel_test_bound {V A : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] [PseudoMetricSpace A] [MeasurableSpace A]
    (G : WDigraph V) (Y : V → A × ℝ × ℝ) (v : V) (H : LimGraph A) (k : ℕ)
    {c d K ε η a C : ℝ} (hG : G.Valid c) (hc : 0≤c) (hd : 0≤d) (hcd : c+d≤1)
    (hq : ∀ i,(Y i).2.1 ∈ Icc (-1:ℝ) 1) (hs : ∀ i,(Y i).2.2=0 ∨ (Y i).2.2=1)
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (hε : 0≤ε) (hη : 0<η) (hmatch : CoupledAt G (fun i => fullMark G (Y i) i) v H k ε)
    (f : FiniteCube k → ℝ) (hf : Continuous f) (hC : 0≤C)
    (hmod : ∀ x y,|f x-f y| ≤ a+C*dist x y) :
    |fixedTestExpectation G (fun i => fullMark G (Y i) i) ζ φ c d k v f -
      limitTestExpectation H ζ φ c d k f| ≤
      a+C*(∑ r : Fin (k+1), (((r:ℝ)+1)*(2*max K 0*ε+η)+(r:ℝ)*(2*ε))) := by
  classical
  let : Fintype (inBall H.toWDigraph 0 k) := (inBall_finite H.toWDigraph 0 k).fintype
  obtain ⟨θ,hroot,hθ,hρ⟩ := hmatch
  obtain ⟨π,hπ,hi,hb⟩ := signal_box_couplings_exist G hG Y hq hs v H k θ ζ φ hζ hφ hKζ hKφ hε hη hρ
  let : ∀ p,IsProbabilityMeasure (π p) := fun p => (hπ p).1
  let F := fun u => boxTrajectory G v (inBall G v k) c d k (pairedBoxLeft θ k u)
  let Q := fun u => boxTrajectory (canonicalGraph H) 0 (inBall H.toWDigraph 0 k) c d k
    (pairedBoxRight (inBall H.toWDigraph 0 k) k u)
  have hF : Measurable F := (boxTrajectory_measurable G v _ c d k).comp (pairedBoxLeft_measurable θ k)
  have hQ : Measurable Q := (boxTrajectory_measurable (canonicalGraph H) 0 _ c d k).comp
    (pairedBoxRight_measurable _ k)
  have hE := expected_cube_distance_bound (Measure.pi π) k F Q hF hQ
    (fun u r => boxTrajectory_mem G v _ c d k _ r)
    (fun u r => boxTrajectory_mem (canonicalGraph H) 0 _ c d k _ r)
    (fun r => ((r:ℝ)+1)*(2*max K 0*ε+η)+(r:ℝ)*(2*ε)) (fun r =>
      paired_box_expected G v H k θ hroot hθ c d (2*ε) (2*max K 0*ε+η) hG hc hd hcd
        (by positivity) (by positivity)
        (matching_weight_bound G hG Y hq hs v H k θ
          (fun n i j hr => (matchingRelation_degree_neighbor G v H k θ hθ n i j hr).1) hρ)
        π hi (fun p => (hb p).le) r (by omega))
  have hFc := (cubeRetraction_continuous k).measurable.comp hF
  have hQc := (cubeRetraction_continuous k).measurable.comp hQ
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hFi : Integrable (fun u => f (cubeRetraction k (F u))) (Measure.pi π) :=
    Integrable.of_bound (hf.measurable.comp hFc).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun u => hM _ (mem_univ _))
  have hQi : Integrable (fun u => f (cubeRetraction k (Q u))) (Measure.pi π) :=
    Integrable.of_bound (hf.measurable.comp hQc).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun u => hM _ (mem_univ _))
  have hDi : Integrable (fun u => dist (cubeRetraction k (F u)) (cubeRetraction k (Q u))) (Measure.pi π) := by
    apply Integrable.of_bound (hFc.dist hQc).aestronglyMeasurable 2
    exact Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,Function.comp_def] using
        cube_diameter k (cubeRetraction k (F u)) (cubeRetraction k (Q u))
  have hh := integral_test_modulus_bound (Measure.pi π)
    (fun u => cubeRetraction k (F u)) (fun u => cubeRetraction k (Q u)) f hC hFi hQi hDi
    (fun u => hmod _ _) hE
  rw [left_box_test_integral G Y v H k θ ζ φ hζ hφ c d π hπ f hf,
    right_box_test_integral G Y v H k θ ζ φ hζ hφ c d π hπ f hf] at hh
  exact hh

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Finset

theorem native_kernel_tolerance {A : Type*} [PseudoMetricSpace A] [MeasurableSpace A]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) {c d K : ℝ}
    (hc : 0≤c) (hd : 0≤d) (hcd : c+d≤1) (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) {δ : ℝ} (hδ : 0<δ) :
    ∃ ε : ℝ,0<ε ∧ ∀ (m : ℕ) (G : WDigraph (Fin (m+1))) (Y : Fin (m+1) → A × ℝ × ℝ)
      (v : Fin (m+1)) (H : LimGraph A), G.Valid c →
      (∀ i,(Y i).2.1 ∈ Icc (-1:ℝ) 1) → (∀ i,(Y i).2.2=0 ∨ (Y i).2.2=1) →
      CoupledAt G (fun i => fullMark G (Y i) i) v H k ε →
      |fixedTestExpectation G (fun i => fullMark G (Y i) i) ζ φ c d k v f -
        limitTestExpectation H ζ φ c d k f| ≤ δ := by
  obtain ⟨C,hC,hmod⟩ := compact_test_linear_modulus hf (by positivity : 0<δ/2)
  let B : ℝ := ∑ r : Fin (k+1), (((r:ℝ)+1)*(2*max K 0+1)+(r:ℝ)*2)
  have hB : 0≤B := sum_nonneg fun r _ => by positivity
  let ε := (δ/2)/(C*B+1)
  have hε : 0<ε := by positivity
  refine ⟨ε,hε,?_⟩
  intro m G Y v H hG hq hs hmatch
  have hh := matched_kernel_test_bound G Y v H k hG hc hd hcd hq hs ζ φ hζ hφ hKζ hKφ
    hε.le hε hmatch f hf hC hmod
  have he : (∑ r : Fin (k+1), (((r:ℝ)+1)*(2*max K 0*ε+ε)+(r:ℝ)*(2*ε))) = B*ε := by
    dsimp only [B]
    rw [sum_mul]
    apply sum_congr rfl
    intro r _
    ring
  rw [he] at hh
  have heq : (C*B+1)*ε=δ/2 := mul_div_cancel₀ _ (by positivity : C*B+1≠0)
  have hnon := hε.le
  nlinarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

theorem good_event_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : Set Ω) (hE : MeasurableSet E)
    (F G : Ω → ℝ) (hF : Integrable F P) (hG : Integrable G P)
    {δ B : ℝ} (hδ : 0≤δ) (hb : ∀ ω,|F ω-G ω|≤B)
    (hgood : ∀ ω∈E,|F ω-G ω|≤δ) :
    |(∫ ω,F ω ∂P)-(∫ ω,G ω ∂P)| ≤ δ+B*P.real Eᶜ := by
  have hpoint : ∀ ω,|F ω-G ω| ≤ δ+Eᶜ.indicator (fun _ => B) ω := by
    intro ω
    by_cases he : ω∈E
    · simpa only [indicator_of_notMem (show ω∉Eᶜ from fun hn => hn he),add_zero] using hgood ω he
    · rw [indicator_of_mem (show ω∈Eᶜ from he)]
      linarith [hb ω]
  have hi : Integrable (Eᶜ.indicator (fun _ : Ω => B)) P := (integrable_const B).indicator hE.compl
  have hh := integral_mono_ae (hF.sub hG).abs ((integrable_const δ).add hi)
    (Filter.Eventually.of_forall hpoint)
  have hadd := integral_add (integrable_const δ : Integrable (fun _ : Ω => δ) P) hi
  simp only [Pi.add_apply] at hh hadd
  rw [hadd,integral_indicator hE.compl,integral_const,setIntegral_const] at hh
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hh
  rw [← integral_sub hF hG]
  exact abs_integral_le_integral_abs.trans (by simpa only [Pi.sub_apply,mul_comm,Measure.real,mul_one] using hh)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set Filter Topology

theorem integral_tendsto_of_good_comparisons {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℕ → Ω → ℝ) (hF : ∀ n,Integrable (F n) P)
    (b B : ℝ)
    (happrox : ∀ δ : ℝ,0<δ → ∃ (G : ℕ → Ω → ℝ) (E : ℕ → Set Ω),
      (∀ n,Integrable (G n) P) ∧ (∀ n,MeasurableSet (E n)) ∧
      (∀ n,(∫ ω,G n ω ∂P)=b) ∧ (∀ n ω,|F n ω-G n ω|≤B) ∧
      (∀ n ω,ω∈E n → |F n ω-G n ω|≤δ) ∧
      Tendsto (fun n => P.real (E n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,F n ω ∂P) atTop (𝓝 b) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨G,E,hG,hE,hb,hbound,hgood,hbad⟩ := happrox (ε/2) (by positivity)
  have ht : Tendsto (fun n => B*P.real (E n)ᶜ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbad.const_mul B
  have he := (tendsto_order.1 ht).2 (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N,?_⟩
  intro n hn
  have hh := good_event_integral_bound P (E n) (hE n) (F n) (G n) (hF n) (hG n)
    (by positivity : 0≤ε/2) (hbound n) (hgood n)
  rw [hb n] at hh
  rw [Real.dist_eq]
  linarith [hN n hn]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem integral_tendsto_of_in_measure_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : ℕ → Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (B c : ℝ)
    (hb : ∀ n, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ B)
    (hlim : TendstoInMeasure P f atTop (fun _ => c)) :
    Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 c) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (show TendstoInMeasure P (fun n => f (ns n)) atTop (fun _ => c) from
    fun ε hε => (hlim ε hε).comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simpa using tendsto_integral_of_dominated_convergence (fun _ : Ω => B)
    (fun n => hf (ns (ms n))) (integrable_const B) (fun n => hb (ns (ms n))) hms

theorem unconditional_bad_event_vanishes {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ n, m n ≤ mΩ) (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (hgood : TendstoInMeasure P (fun n => P[(E n).indicator (fun _ => (1 : ℝ)) | m n])
      atTop (fun _ => 1)) :
    Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0) := by
  have hlow : ∀ n, 0 ≤ᵐ[P] P[(E n).indicator (fun _ => (1 : ℝ)) | m n] := by
    intro n
    apply condExp_nonneg
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ E n <;> simp [hω]
  have hupp : ∀ n, P[(E n).indicator (fun _ => (1 : ℝ)) | m n] ≤ᵐ[P] (fun _ => 1) := by
    intro n
    have h := condExp_mono ((integrable_const (μ := P) (1:ℝ)).indicator (hE n)) (integrable_const (μ := P) (1:ℝ))
      (Filter.Eventually.of_forall (fun ω => show (E n).indicator (fun _ => (1:ℝ)) ω ≤ 1 by
        by_cases hω : ω ∈ E n <;> simp [hω])) (m := m n)
    simpa only [condExp_const (hm n)] using h
  have hb : ∀ n, ∀ᵐ ω ∂P, ‖P[(E n).indicator (fun _ => (1 : ℝ)) | m n] ω‖ ≤ 1 := by
    intro n
    filter_upwards [hlow n, hupp n] with ω hlo hhi
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  have hint := integral_tendsto_of_in_measure_bounded P
    (fun n => P[(E n).indicator (fun _ => (1 : ℝ)) | m n])
    (fun _ => integrable_condExp.aestronglyMeasurable) 1 1 hb hgood
  have hid : ∀ n, (∫ ω, P[(E n).indicator (fun _ => (1 : ℝ)) | m n] ω ∂P) = P.real (E n) := by
    intro n
    rw [integral_condExp (hm n), integral_indicator_const 1 (hE n)]
    simp
  simp_rw [hid] at hint
  have hc : Tendsto (fun n => P.real (E n)ᶜ) atTop (𝓝 0) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hint
    have he : ∀ n, P.real (E n)ᶜ = 1 - P.real (E n) := by
      intro n
      simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using measureReal_compl (μ := P) (hE n)
    simpa only [he, sub_self] using this
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hc
  simpa only [Function.comp_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_zero] using ho

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_first_test_moment {Ω A : Type*} [mΩ : MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
    (k : ℕ) (hk : 1≤k) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) ∂P)
      atTop (𝓝 (∫ H,limitTestExpectation H ζ φ c d k f ∂μ)) := by
  let F := fun m ω => fixedTestExpectation (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) f
  let L := fun H : LimGraph A => limitTestExpectation H ζ φ c d k f
  have hL : Measurable L := limitTestExpectation_measurable ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf
  obtain ⟨M,hM,hbound⟩ := compact_test_bound f hf
  have hFb : ∀ m ω,|F m ω|≤M := fun m ω => fixedTestExpectation_bound _ _ _ _ _ _ _ _ _ hM hbound
  have hLb : ∀ H,|L H|≤M := fun H => fixedTestExpectation_bound _ _ _ _ _ _ _ _ _ hM hbound
  have hFm : ∀ m,Measurable (F m) := by
    intro m
    exact (nativeTestExpectation_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf).comp
      (((hS.measurable_I m).prodMk (hS.measurable_graph m)).mono (hS.le m) le_rfl)
  have hFi : ∀ m,Integrable (F m) P := fun m => Integrable.of_bound (hFm m).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hFb m ω)
  have ht : Tendsto (fun m => ∫ ω,F m ω ∂P) atTop (𝓝 (∫ H,L H ∂μ)) := by
    apply integral_tendsto_of_good_comparisons P F hFi (∫ H,L H ∂μ) (2*M)
    intro δ hδ
    obtain ⟨ε,hε,he⟩ := native_kernel_tolerance ζ φ hS.measurable_ζ hS.measurable_φ
      hS.c_nonneg hS.d_pos.le hS.cd_le_one hKζ hKφ k f hf hδ
    obtain ⟨H,H',E,E',hH,hH',hl,hl',hind,hE,hE',hmatch,hmatch',hdis,hgood⟩ := hSC k hk ε hε
    let B := fun m => E m ∩ E' m
    have hBm : ∀ m,MeasurableSet (B m) := fun m => (hS.le m) _ ((hE m).inter (hE' m))
    have hGi : ∀ m,Integrable (fun ω => L (H m ω)) P := fun m =>
      Integrable.of_bound (hL.comp ((hH m).mono (hS.le m) le_rfl)).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hLb (H m ω))
    refine ⟨(fun m ω => L (H m ω)),B,hGi,hBm,?_,?_,?_,?_⟩
    · intro m
      exact (hl m).integral_comp hL.aestronglyMeasurable
    · intro m ω
      have hh := abs_sub_le (F m ω) 0 (L (H m ω))
      simp only [sub_zero,zero_sub,abs_neg] at hh
      linarith [hFb m ω,hLb (H m ω)]
    · intro m ω hω
      exact he m (S.G m ω) (fun i => S.Y m i ω) (S.I m ω) (H m ω) (hS.valid m ω)
        (fun i => hS.q_mem m i ω) (fun i => hS.s_mem m i ω) (hmatch m hω.1)
    · have hAle : ∀ m,S.𝓐 m ≤ mΩ := fun m => Measurable.comap_le
        ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl)
      have ht := unconditional_bad_event_vanishes P S.𝓐 hAle B hBm hgood
      exact (ENNReal.continuousAt_toReal (by norm_num : (0:ENNReal)≠⊤)).tendsto.comp ht
  have hid : (fun m => ∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) ∂P) =
      (fun m => ∫ ω,F m ω ∂P) := by
    funext m
    exact native_test_noise_average P S 𝓖 ζ φ c d hS m k f hf
  rw [hid]
  exact ht

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def pairTestExpectation {V A : Type*} (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (v w : V) (f : FiniteCube k → ℝ) : ℝ :=
  ∫ u,f (cubeRetraction k (fixedTrajectory G ξ ζ φ c d k v u)) *
    f (cubeRetraction k (fixedTrajectory G ξ ζ φ c d k w u)) ∂vertexNoiseLaw V

theorem native_pair_noise_average {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    (∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) *
      f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.J m ω))) ∂P) =
    ∫ ω,pairTestExpectation (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) (S.J m ω) f ∂P := by
  let T := fun ω => (S.I m ω,(S.J m ω,S.graphData m ω))
  have hT : Measurable[𝓖 m] T := (hS.measurable_I m).prodMk
    ((hS.measurable_J m).prodMk (hS.measurable_graph m))
  let F := fun p : (Fin (m+1) × (Fin (m+1) × NativeGraphData A m)) ×
      (Option ℕ × Fin (m+1) → ℝ) =>
    nativeTrajectoryTest ζ φ c d k f ((p.1.1,p.1.2.2),p.2) *
      nativeTrajectoryTest ζ φ c d k f ((p.1.2.1,p.1.2.2),p.2)
  have hm0 := nativeTrajectoryTest_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf
  have hm : Measurable F := (hm0.comp (by fun_prop)).mul (hm0.comp (by fun_prop))
  obtain ⟨M,hM,hb⟩ := compact_test_bound f hf
  have hi : Integrable F ((P.map T).prod (finiteVertexNoiseLaw m)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (M*M)
    apply Filter.Eventually.of_forall
    intro p
    change |f _ * f _| ≤ M*M
    rw [abs_mul]
    exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hM
  have he := independent_noise_integral P (finiteVertexNoiseLaw m) T (fun ω p => S.unif m p ω)
    (hT.mono (hS.le m) le_rfl) (native_noise_hasLaw P S 𝓖 ζ φ c d hS m)
    (native_noise_indep_struct_function P S 𝓖 ζ φ c d hS m T hT).symm F hm hi
  convert he using 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [F,T,nativeTrajectoryTest]
    congr 3 <;> funext r <;>
      exact (nativeKernelOpinion_actual P S 𝓖 ζ φ c d hS m r ω _).symm
  · rfl

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

theorem pairTestExpectation_bound {V A : Type*} (G : WDigraph V) (ξ : V → Mark A)
    (ζ φ : Mark A → ℝ → ℝ) (c d : ℝ) (k : ℕ) (v w : V) (f : FiniteCube k → ℝ)
    {M : ℝ} (hM : 0≤M) (hb : ∀ x,|f x|≤M) :
    |pairTestExpectation G ξ ζ φ c d k v w f| ≤ M*M := by
  apply integral_abs_le_bound (vertexNoiseLaw V) _ (mul_nonneg hM hM)
  intro u
  rw [abs_mul]
  exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hM

theorem pairTestExpectation_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ)
    (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Measurable (fun p : Fin (m+1) × (Fin (m+1) × NativeGraphData A m) =>
      pairTestExpectation (decodeNativeGraph p.2.2) (decodeNativeMark p.2.2) ζ φ c d k p.1 p.2.1 f) := by
  let F := fun p : (Fin (m+1) × (Fin (m+1) × NativeGraphData A m)) ×
      (Option ℕ × Fin (m+1) → ℝ) =>
    nativeTrajectoryTest ζ φ c d k f ((p.1.1,p.1.2.2),p.2) *
      nativeTrajectoryTest ζ φ c d k f ((p.1.2.1,p.1.2.2),p.2)
  have hm0 := nativeTrajectoryTest_measurable m ζ φ hζ hφ c d k f hf
  have hm : Measurable F := (hm0.comp (by fun_prop)).mul (hm0.comp (by fun_prop))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := finiteVertexNoiseLaw m)).measurable

theorem product_difference_bound {a b x y M δ : ℝ} (hM : 0≤M) (hδ : 0≤δ)
    (ha : |a|≤M) (hy : |y|≤M) (hax : |a-x|≤δ) (hby : |b-y|≤δ) :
    |a*b-x*y| ≤ 2*M*δ := by
  have he : a*b-x*y=a*(b-y)+(a-x)*y := by ring
  rw [he]
  have hb := abs_add_le (a*(b-y)) ((a-x)*y)
  rw [abs_mul,abs_mul] at hb
  have h1 := mul_le_mul ha hby (abs_nonneg _) hM
  have h2 := mul_le_mul hax hy (abs_nonneg _) hδ
  nlinarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_pair_test_moment {Ω A : Type*} [mΩ : MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
    (k : ℕ) (hk : 1≤k) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) * f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.J m ω))) ∂P)
      atTop (𝓝 ((∫ H,limitTestExpectation H ζ φ c d k f ∂μ)^2)) := by
  let F := fun m ω => pairTestExpectation (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) (S.J m ω) f
  let L := fun H : LimGraph A => limitTestExpectation H ζ φ c d k f
  have hL : Measurable L := limitTestExpectation_measurable ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf
  obtain ⟨M,hM,hbound⟩ := compact_test_bound f hf
  have hFb : ∀ m ω,|F m ω|≤M*M := fun m ω => pairTestExpectation_bound _ _ _ _ _ _ _ _ _ _ hM hbound
  have hLb : ∀ H,|L H|≤M := fun H => fixedTestExpectation_bound _ _ _ _ _ _ _ _ _ hM hbound
  have hFm : ∀ m,Measurable (F m) := by
    intro m
    exact (pairTestExpectation_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf).comp
      (((hS.measurable_I m).prodMk ((hS.measurable_J m).prodMk (hS.measurable_graph m))).mono (hS.le m) le_rfl)
  have hFi : ∀ m,Integrable (F m) P := fun m => Integrable.of_bound (hFm m).aestronglyMeasurable (M*M)
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hFb m ω)
  have ht : Tendsto (fun m => ∫ ω,F m ω ∂P) atTop (𝓝 ((∫ H,L H ∂μ)^2)) := by
    apply integral_tendsto_of_good_comparisons P F hFi ((∫ H,L H ∂μ)^2) (2*(M*M))
    intro δ hδ
    let δ' := δ/(2*M+1)
    have hδ' : 0<δ' := by positivity
    obtain ⟨ε,hε,he⟩ := native_kernel_tolerance ζ φ hS.measurable_ζ hS.measurable_φ
      hS.c_nonneg hS.d_pos.le hS.cd_le_one hKζ hKφ k f hf hδ'
    obtain ⟨H,H',E,E',hH,hH',hl,hl',hind,hE,hE',hmatch,hmatch',hdis,hgood⟩ := hSC k hk ε hε
    let B := fun m => E m ∩ E' m
    have hBm : ∀ m,MeasurableSet (B m) := fun m => (hS.le m) _ ((hE m).inter (hE' m))
    have hGa : ∀ m,Measurable (fun ω => L (H m ω)) := fun m => hL.comp ((hH m).mono (hS.le m) le_rfl)
    have hGb : ∀ m,Measurable (fun ω => L (H' m ω)) := fun m => hL.comp ((hH' m).mono (hS.le m) le_rfl)
    have hprod : ∀ m ω,|L (H m ω)*L (H' m ω)|≤M*M := by
      intro m ω
      rw [abs_mul]
      exact mul_le_mul (hLb _) (hLb _) (abs_nonneg _) hM
    have hGi : ∀ m,Integrable (fun ω => L (H m ω)*L (H' m ω)) P := fun m =>
      Integrable.of_bound ((hGa m).mul (hGb m)).aestronglyMeasurable (M*M)
        (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hprod m ω)
    refine ⟨(fun m ω => L (H m ω)*L (H' m ω)),B,hGi,hBm,?_,?_,?_,?_⟩
    · intro m
      have hi := (hind m).comp hL hL
      have heq := hi.integral_fun_mul_eq_mul_integral (hGa m).aestronglyMeasurable (hGb m).aestronglyMeasurable
      simp only [Function.comp_def] at heq
      have ha := (hl m).integral_comp hL.aestronglyMeasurable
      have hb := (hl' m).integral_comp hL.aestronglyMeasurable
      simp only [Function.comp_def] at ha hb
      rw [ha,hb] at heq
      simpa only [pow_two] using heq
    · intro m ω
      have hh := abs_sub_le (F m ω) 0 (L (H m ω)*L (H' m ω))
      simp only [sub_zero,zero_sub,abs_neg] at hh
      linarith [hFb m ω,hprod m ω]
    · intro m ω hω
      have ha := he m (S.G m ω) (fun i => S.Y m i ω) (S.I m ω) (H m ω) (hS.valid m ω)
        (fun i => hS.q_mem m i ω) (fun i => hS.s_mem m i ω) (hmatch m hω.1)
      have hb := he m (S.G m ω) (fun i => S.Y m i ω) (S.J m ω) (H' m ω) (hS.valid m ω)
        (fun i => hS.q_mem m i ω) (fun i => hS.s_mem m i ω) (hmatch' m hω.2)
      have hpair := disjoint_test_factorization (S.G m ω) (fun i => S.mark m i ω) ζ φ
        hS.measurable_ζ hS.measurable_φ c d k (S.I m ω) (S.J m ω) (hdis m hω) f f hf hf
      change |pairTestExpectation _ _ _ _ _ _ _ _ _ _ - _| ≤ δ
      rw [show pairTestExpectation (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) (S.J m ω) f = _ from hpair]
      have hh := product_difference_bound hM hδ'.le
        (fixedTestExpectation_bound (S.G m ω) (fun i => S.mark m i ω) ζ φ c d k (S.I m ω) f hM hbound)
        (hLb (H' m ω)) ha hb
      have heq : (2*M+1)*δ'=δ := mul_div_cancel₀ _ (by positivity : 2*M+1≠0)
      exact hh.trans (by nlinarith)
    · have hAle : ∀ m,S.𝓐 m ≤ mΩ := fun m => Measurable.comap_le
        ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl)
      have ht := unconditional_bad_event_vanishes P S.𝓐 hAle B hBm hgood
      exact (ENNReal.continuousAt_toReal (by norm_num : (0:ENNReal)≠⊤)).tendsto.comp ht
  have hid : (fun m => ∫ ω,f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) * f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.J m ω))) ∂P) =
      (fun m => ∫ ω,F m ω ∂P) := by
    funext m
    exact native_pair_noise_average P S 𝓖 ζ φ c d hS m k f hf
  rw [hid]
  exact ht

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Filter Topology

def cubePrefix (k : ℕ) (x : FiniteCube (k+1)) : FiniteCube k := fun i => x i.castSucc

theorem cubePrefix_continuous (k : ℕ) : Continuous (cubePrefix k) :=
  continuous_pi (fun i => continuous_apply i.castSucc)

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
variable (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
variable (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
include hS hKζ hKφ hSC

theorem native_first_test_moment_all_depths (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω, f (cubeRetraction k
      (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) ∂P)
      atTop (𝓝 (∫ H, limitTestExpectation H ζ φ c d k f ∂μ)) := by
  exact native_first_test_moment P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC (k+1) (by omega)
    (fun x => f (cubePrefix k x)) (hf.comp (cubePrefix_continuous k))

theorem native_pair_test_moment_all_depths (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω, f (cubeRetraction k
      (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) *
      f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.J m ω))) ∂P)
      atTop (𝓝 ((∫ H, limitTestExpectation H ζ φ c d k f ∂μ)^2)) := by
  exact native_pair_test_moment P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC (k+1) (by omega)
    (fun x => f (cubePrefix k x)) (hf.comp (cubePrefix_continuous k))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem abs_le_eps_add_sq_div (x ε : ℝ) (hε : 0 < ε) :
    |x| ≤ ε + x ^ 2 / ε := by
  have hsq := sq_nonneg (|x| - ε)
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  calc
    |x| ≤ (ε ^ 2 + x ^ 2) / ε := (le_div_iff₀ hε).2 (by nlinarith)
    _ = ε + x ^ 2 / ε := by field_simp

theorem integral_abs_le_eps_add_integral_sq_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ)
    (hf : Integrable f P) (hf2 : Integrable (fun ω => f ω ^ 2) P)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ ω, |f ω| ∂P) ≤ ε + (∫ ω, f ω ^ 2 ∂P) / ε := by
  calc
    (∫ ω, |f ω| ∂P) ≤ ∫ ω, ε + f ω ^ 2 / ε ∂P :=
      integral_mono hf.abs ((integrable_const ε).add (hf2.div_const ε))
        (fun ω => abs_le_eps_add_sq_div (f ω) ε hε)
    _ = ε + (∫ ω, f ω ^ 2 ∂P) / ε := by
      rw [integral_add (integrable_const ε) (hf2.div_const ε), integral_div]
      simp

theorem integral_abs_tendsto_zero_of_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : ℕ → Ω → ℝ)
    (hf : ∀ n, Integrable (f n) P)
    (hf2 : ∀ n, Integrable (fun ω => f n ω ^ 2) P)
    (hlim : Tendsto (fun n => ∫ ω, f n ω ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω| ∂P) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun ω => abs_nonneg _)
  · intro b hb
    have hd : 0 < b / 2 := by positivity
    filter_upwards [hlim.eventually (gt_mem_nhds (sq_pos_of_pos hd))] with n hn
    have hbound := integral_abs_le_eps_add_integral_sq_div P (f n) (hf n) (hf2 n) (b / 2) hd
    have hdiv : (∫ ω, f n ω ^ 2 ∂P) / (b / 2) < b / 2 :=
      (div_lt_iff₀ hd).2 (by nlinarith [hn])
    linarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Filter Topology

theorem moments_to_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (hF : ∀ n,Integrable (F n) P)
    (hF2 : ∀ n,Integrable (fun ω => (F n ω)^2) P) (b : ℝ)
    (h1 : Tendsto (fun n => ∫ ω,F n ω ∂P) atTop (𝓝 b))
    (h2 : Tendsto (fun n => ∫ ω,(F n ω)^2 ∂P) atTop (𝓝 (b^2))) :
    Tendsto (fun n => ∫ ω,(F n ω-b)^2 ∂P) atTop (𝓝 0) := by
  have he : ∀ n,(∫ ω,(F n ω-b)^2 ∂P) = (∫ ω,(F n ω)^2 ∂P)-2*b*(∫ ω,F n ω ∂P)+b^2 := by
    intro n
    have hp : (fun ω => (F n ω-b)^2) = fun ω => (F n ω)^2-(2*b)*F n ω+b^2 := by
      funext ω; ring
    have ha := integral_add ((hF2 n).sub ((hF n).const_mul (2*b))) (integrable_const (b^2) : Integrable (fun _ : Ω => b^2) P)
    have hs := integral_sub (hF2 n) ((hF n).const_mul (2*b))
    simp only [Pi.sub_apply] at ha hs
    rw [hp,ha,hs,integral_const_mul,integral_const]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  simp_rw [he]
  have hh := (h2.sub (h1.const_mul (2*b))).add_const (b^2)
  have he0 : b^2-2*b*b+b^2=0 := by ring
  simpa only [he0] using hh

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω A : Type*} [MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
variable (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
variable (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
include hS hKζ hKφ hSC

theorem native_empirical_trajectory_l2 (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω, (nativeTrajectoryEmpirical S ζ φ c d k f m ω -
      ∫ H, limitTestExpectation H ζ φ c d k f ∂μ)^2 ∂P) atTop (𝓝 0) := by
  have hint := nativeTrajectoryEmpirical_integrable P S 𝓖 ζ φ c d hS k f hf
  have hmean : ∀ m, (∫ ω, nativeTrajectoryEmpirical S ζ φ c d k f m ω ∂P) =
      ∫ ω, f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) ∂P :=
    fun m => (native_trajectory_empirical_moment_identities P S 𝓖 ζ φ c d hS m k f hf).1
  have hsquare : ∀ m, (∫ ω, (nativeTrajectoryEmpirical S ζ φ c d k f m ω)^2 ∂P) =
      ∫ ω, f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.I m ω))) *
        f (cubeRetraction k (fun r : Fin (k+1) => S.R ζ φ c d m r ω (S.J m ω))) ∂P :=
    fun m => (native_trajectory_empirical_moment_identities P S 𝓖 ζ φ c d hS m k f hf).2
  apply moments_to_l2 P (nativeTrajectoryEmpirical S ζ φ c d k f)
    (fun m => (hint m).1) (fun m => (hint m).2)
  · simp_rw [hmean]
    exact native_first_test_moment_all_depths P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f hf
  · simp_rw [hsquare]
    exact native_pair_test_moment_all_depths P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f hf

theorem native_empirical_trajectory_l1 (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    Tendsto (fun m => ∫ ω, |nativeTrajectoryEmpirical S ζ φ c d k f m ω -
      ∫ H, limitTestExpectation H ζ φ c d k f ∂μ| ∂P) atTop (𝓝 0) := by
  let b := ∫ H, limitTestExpectation H ζ φ c d k f ∂μ
  have hint := nativeTrajectoryEmpirical_integrable P S 𝓖 ζ φ c d hS k f hf
  have hc2 : ∀ m, Integrable (fun ω => (nativeTrajectoryEmpirical S ζ φ c d k f m ω-b)^2) P := by
    intro m
    have hi := (((hint m).2).sub (((hint m).1).const_mul (2*b))).add
      (integrable_const (b^2) : Integrable (fun _ : Ω => b^2) P)
    apply hi.congr
    filter_upwards [] with ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  exact integral_abs_tendsto_zero_of_sq P
    (fun m ω => nativeTrajectoryEmpirical S ζ φ c d k f m ω-b)
    (fun m => (hint m).1.sub (integrable_const b)) hc2
    (native_empirical_trajectory_l2 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f hf)

theorem native_empirical_trajectory_in_measure (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (nativeTrajectoryEmpirical S ζ φ c d k f) atTop
      (fun _ => ∫ H, limitTestExpectation H ζ φ c d k f ∂μ) := by
  exact in_measure_of_integral_abs_sub_const P (nativeTrajectoryEmpirical S ζ φ c d k f)
    (fun m => (nativeTrajectoryEmpirical_integrable P S 𝓖 ζ φ c d hS k f hf m).1) _
    (native_empirical_trajectory_l1 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f hf)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
variable (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
variable (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
include hS hKζ hKφ hSC

theorem native_finite_conditional_test (k : ℕ) (f : FiniteCube k → ℝ) (hf : Continuous f) :
    TendstoInMeasure P (fun m ω => ∫ x,f (cubeRetraction k x) ∂trajCondLaw P S ζ φ c d m k ω)
      atTop (fun _ => ∫ x,f (cubeRetraction k x)
        ∂(auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))) := by
  rw [auxiliary_test_integral μ ζ φ hS.measurable_ζ hS.measurable_φ c d k f hf]
  apply conditional_test_in_measure_of_ae_eq P S.𝓐
    (fun m => ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl).comap_le)
    (nativeTrajectoryEmpirical S ζ φ c d k f) _
    (fun m => (nativeTrajectoryEmpirical_integrable P S 𝓖 ζ φ c d hS k f hf m).1)
  · intro m
    exact native_trajectory_conditional_identity P S 𝓖 ζ φ c d hS m k f hf
  · exact native_empirical_trajectory_l1 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f hf

theorem native_finite_conditional_W1 (k : ℕ) (ε : ℝ) (hε : 0<ε) :
    Tendsto (fun m => P {ω | ENNReal.ofReal ε ≤ W1vec (trajCondLaw P S ζ φ c d m k ω)
      (auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))})
      atTop (𝓝 0) := by
  apply finite_cube_transport_in_probability P k (fun m ω => nativeTrajectoryCondProbability P S ζ φ c d m k ω)
    (auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k)
  · intro m
    exact native_trajectory_cond_support P S 𝓖 ζ φ c d hS m k
  · exact auxiliaryTrajectoryLaw_supported μ ζ φ hS.measurable_ζ hS.measurable_φ c d k
  · intro f
    exact native_finite_conditional_test P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f f.continuous
  · exact hε

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory Set

noncomputable def extendTest (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (clip (-1) 1 x)

theorem extendTest_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    Continuous (extendTest f) :=
  hf.comp_continuous (continuous_clip (-1) 1) (clip_mem (by norm_num))

theorem extendTest_eq {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (-1:ℝ) 1) :
    extendTest f x = f x := by rw [extendTest, clip_eq hx]

theorem continuousOn_supported_integral {f : ℝ → ℝ} (_hf : ContinuousOn f (Icc (-1:ℝ) 1))
    (μ : Measure ℝ) (hs : ∀ᵐ x ∂μ, x ∈ Icc (-1:ℝ) 1) :
    ∫ x, f x ∂μ = ∫ x, extendTest f x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  exact (extendTest_eq hx).symm

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_finite_empirical_scalar {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
    (k : ℕ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    TendstoInMeasure P (fun m ω => empAvg f (S.R ζ φ c d m k ω)) atTop
      (fun _ => ∫ y,f (y (Fin.last k))
        ∂(auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))) := by
  let g : FiniteCube k → ℝ := fun x => extendTest f (x (Fin.last k))
  have hg : Continuous g := (extendTest_continuous hf).comp
    (continuous_subtype_val.comp (continuous_apply (Fin.last k)))
  have he : ∀ x : Fin (k+1) → ℝ,(∀ r,x r∈Icc (-1:ℝ) 1) →
      g (cubeRetraction k x)=f (x (Fin.last k)) := by
    intro x hx
    change extendTest f (clip (-1) 1 (x (Fin.last k))) = _
    rw [clip_eq (hx _),extendTest_eq (hx _)]
  have ha : nativeTrajectoryEmpirical S ζ φ c d k g =
      fun m ω => empAvg f (S.R ζ φ c d m k ω) := by
    funext m ω
    unfold nativeTrajectoryEmpirical empAvg
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact he _ (fun r => native_opinion_mem P S 𝓖 ζ φ c d hS m r ω i)
  have hb := auxiliary_test_integral μ ζ φ hS.measurable_ζ hS.measurable_φ c d k g hg
  have hi : (∫ x,g (cubeRetraction k x)
      ∂(auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))) =
      ∫ x,f (x (Fin.last k)) ∂(auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ)) := by
    apply integral_congr_ae
    filter_upwards [auxiliaryTrajectoryLaw_supported μ ζ φ hS.measurable_ζ hS.measurable_φ c d k] with x hx
    exact he x hx
  have ht := native_empirical_trajectory_in_measure P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k g hg
  rw [ha,← hb,hi] at ht
  exact ht

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_finite_branch {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ) :
    ∀ k : ℕ,
      (∀ η : ℝ,0<η → Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
        W1vec (trajCondLaw P S ζ φ c d m k ω)
          (auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))})
        atTop (𝓝 0)) ∧
      ∀ f : ℝ → ℝ,ContinuousOn f (Icc (-1:ℝ) 1) →
        TendstoInMeasure P (fun m ω => empAvg f (S.R ζ φ c d m k ω)) atTop
          (fun _ => ∫ y,f (y (Fin.last k))
            ∂(auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure (Fin (k+1) → ℝ))) := by
  intro k
  exact ⟨native_finite_conditional_W1 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k,
    native_finite_empirical_scalar P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k⟩

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Filter Topology

theorem compact_stationary_limit_of_endpoint_couplings {X : Type*} [MetricSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → ℕ → ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure X)
    (L : ℕ → ProbabilityMeasure X)
    (hμ : ∀ k, Tendsto (fun n => μ n k) atTop (𝓝 (L k))) (a : ℕ → ℝ)
    (hcoupling : ∀ n k, ∃ π : ProbabilityMeasure (X × X),
      IsCoupling (π : Measure (X × X)) (μ n k : Measure X) (ν n : Measure X) ∧
      (∫ z, dist z.1 z.2 ∂(π : Measure (X × X))) ≤ a k) :
    ∃ Lstar : ProbabilityMeasure X, ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ Tendsto (ν ∘ σ) atTop (𝓝 Lstar) ∧
      ∀ k, ∃ π : ProbabilityMeasure (X × X),
        IsCoupling (π : Measure (X × X)) (L k : Measure X) (Lstar : Measure X) ∧
        (∫ z, dist z.1 z.2 ∂(π : Measure (X × X))) ≤ a k := by
  obtain ⟨Lstar, σ, hσ, hν⟩ := CompactSpace.tendsto_subseq ν
  refine ⟨Lstar, σ, hσ, hν, ?_⟩
  intro k
  choose π hπ hc using (fun n => hcoupling (σ n) k)
  exact compact_coupling_limit (fun n => μ (σ n) k) (ν ∘ σ) (L k) Lstar
    ((hμ k).comp hσ.tendsto_atTop) hν π hπ
    ⟨fun z => dist z.1 z.2, continuous_dist⟩ (fun _ => a k) (a k) tendsto_const_nhds hc

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem compact_coupling_test_modulus {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (f : C(X, ℝ)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : ProbabilityMeasure X) (π : ProbabilityMeasure (X × X)),
      IsCoupling (π : Measure (X × X)) (μ : Measure X) (ν : Measure X) →
      |(∫ x, f x ∂(μ : Measure X)) - ∫ x, f x ∂(ν : Measure X)| ≤
        η + C * ∫ z, dist z.1 z.2 ∂(π : Measure (X × X)) := by
  obtain ⟨C, hC, hmod⟩ := compact_test_linear_modulus f.continuous hη
  refine ⟨C, hC, ?_⟩
  intro μ ν π hπ
  have hd : Integrable (fun z : X × X => dist z.1 z.2) (π : Measure (X × X)) :=
    continuous_dist.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg := (integrable_const η).add (hd.const_mul C)
  have h := coupling_integral_test_bound hπ f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hg
    (Filter.Eventually.of_forall fun z => hmod z.1 z.2)
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const η) (hd.const_mul C), integral_const_mul] at h
  simpa using h

theorem compact_weak_convergence_of_coupling_cost {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ℕ → ProbabilityMeasure X) (ν : ProbabilityMeasure X)
    (π : ℕ → ProbabilityMeasure (X × X))
    (hπ : ∀ n, IsCoupling (π n : Measure (X × X)) (μ n : Measure X) (ν : Measure X))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hc : ∀ n, (∫ z, dist z.1 z.2 ∂(π n : Measure (X × X))) ≤ a n) :
    Tendsto μ atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨C, hC, hb⟩ := compact_coupling_test_modulus (⟨f, f.continuous⟩ : C(X, ℝ))
    (by positivity : 0 < ε/2)
  have hca : Tendsto (fun n => C * a n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ha
  filter_upwards [hca.eventually (gt_mem_nhds (by positivity : 0 < ε/2))] with n hn
  have hbound := (hb (μ n) ν (π n) (hπ n)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hc n) hC))
  rw [Real.dist_eq]
  change |(∫ x, f x ∂(μ n : Measure X)) - ∫ x, f x ∂(ν : Measure X)| < ε
  change |(∫ x, f x ∂(μ n : Measure X)) - ∫ x, f x ∂(ν : Measure X)| ≤ _ at hbound
  linarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem compact_stationary_full_convergence {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → ℕ → ProbabilityMeasure X) (ν : ℕ → ProbabilityMeasure X)
    (L : ℕ → ProbabilityMeasure X) (Lstar : ProbabilityMeasure X)
    (hμ : ∀ k, Tendsto (fun n => μ n k) atTop (𝓝 (L k))) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0))
    (hfinite : ∀ n k, ∃ π : ProbabilityMeasure (X × X),
      IsCoupling (π : Measure (X × X)) (μ n k : Measure X) (ν n : Measure X) ∧
      (∫ z, dist z.1 z.2 ∂(π : Measure (X × X))) ≤ a k)
    (hlimit : ∀ k, ∃ π : ProbabilityMeasure (X × X),
      IsCoupling (π : Measure (X × X)) (L k : Measure X) (Lstar : Measure X) ∧
      (∫ z, dist z.1 z.2 ∂(π : Measure (X × X))) ≤ a k) :
    Tendsto ν atTop (𝓝 Lstar) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  let fc : C(X, ℝ) := ⟨f, f.continuous⟩
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨C, hC, hb⟩ := compact_coupling_test_modulus fc (by positivity : 0 < ε/6)
  have hca : Tendsto (fun k => C*a k) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ha
  obtain ⟨k, hk⟩ := (hca.eventually (gt_mem_nhds (by positivity : 0 < ε/6))).exists
  obtain ⟨πk, hπk, hck⟩ := hlimit k
  have hkbound := (hb (L k) Lstar πk hπk).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hck hC))
  have htest : Tendsto (fun n => ∫ x, fc x ∂(μ n k : Measure X)) atTop
      (𝓝 (∫ x, fc x ∂(L k : Measure X))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap fc).tendsto (L k) |>.comp (hμ k)
  filter_upwards [Metric.tendsto_nhds.1 htest (ε/3) (by positivity)] with n hn
  obtain ⟨πn, hπn, hcn⟩ := hfinite n k
  have hnbound := (hb (μ n k) (ν n) πn hπn).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcn hC))
  have htri1 := abs_sub_le (∫ x, fc x ∂(ν n : Measure X))
    (∫ x, fc x ∂(μ n k : Measure X)) (∫ x, fc x ∂(Lstar : Measure X))
  have htri2 := abs_sub_le (∫ x, fc x ∂(μ n k : Measure X))
    (∫ x, fc x ∂(L k : Measure X)) (∫ x, fc x ∂(Lstar : Measure X))
  rw [Real.dist_eq] at hn ⊢
  rw [abs_sub_comm] at hnbound
  change |(∫ x, fc x ∂(ν n : Measure X)) - ∫ x, fc x ∂(Lstar : Measure X)| < ε
  linarith

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Filter Topology

theorem stationary_rate_tendsto_zero {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    Tendsto (fun k : ℕ => (1-d)^k * (1+1/d)) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1-d) (by linarith : 1-d < 1)
  simpa using hpow.mul_const (1+1/d)

theorem stationary_rate_le_native_rate {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (k : ℕ) :
    (1-d)^k * (1+1/d) ≤ (1-d)^k * (2/d+2) := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) k)
  have hp : 0 < 1/d := one_div_pos.mpr hd
  have he : 2/d = 2*(1/d) := by ring
  rw [he]
  linarith

theorem native_stationary_limit_package {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (L : ℕ → ProbabilityMeasure OpinionInterval)
    (hL : ∀ k, Tendsto (fun m => nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k)
      atTop (𝓝 (L k))) :
    ∃ Lstar : ProbabilityMeasure OpinionInterval,
      Tendsto (nativeCompactStationaryLaw P S 𝓖 ζ φ c d hS) atTop (𝓝 Lstar) ∧
      Tendsto L atTop (𝓝 Lstar) ∧
      ∀ k, ∃ π : ProbabilityMeasure (OpinionInterval × OpinionInterval),
        IsCoupling (π : Measure (OpinionInterval × OpinionInterval))
          (L k : Measure OpinionInterval) (Lstar : Measure OpinionInterval) ∧
        (∫ z, dist z.1 z.2 ∂(π : Measure (OpinionInterval × OpinionInterval))) ≤
          (1-d)^k * (1+1/d) := by
  let a : ℕ → ℝ := fun k => (1-d)^k * (1+1/d)
  have ha : Tendsto a atTop (𝓝 0) := stationary_rate_tendsto_zero hS.d_pos hS.d_le_one
  have hfinite := native_endpoint_stationary_compact_coupling P S 𝓖 ζ φ c d hS
  obtain ⟨Lstar, _, _, _, hstar⟩ := compact_stationary_limit_of_endpoint_couplings
    (nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS)
    (nativeCompactStationaryLaw P S 𝓖 ζ φ c d hS) L hL a hfinite
  have hfull := compact_stationary_full_convergence
    (nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS)
    (nativeCompactStationaryLaw P S 𝓖 ζ φ c d hS) L Lstar hL a ha hfinite hstar
  choose π hπ hc using hstar
  exact ⟨Lstar, hfull, compact_weak_convergence_of_coupling_cost L Lstar π hπ a ha hc,
    fun k => ⟨π k, hπ k, hc k⟩⟩

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

noncomputable def auxiliaryCompactEndpointLaw {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) : ProbabilityMeasure OpinionInterval :=
  (auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k).map
    ((scalarOpinionClamp_continuous.comp (continuous_apply (Fin.last k) : Continuous (fun x : Fin (k+1) → ℝ => x (Fin.last k)))).measurable.aemeasurable)

theorem auxiliary_endpoint_test_integral {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) (f : C(OpinionInterval, ℝ)) :
    (∫ x, f x ∂(auxiliaryCompactEndpointLaw μ ζ φ hζ hφ c d k : Measure OpinionInterval)) =
      ∫ H, limitTestExpectation H ζ φ c d k (fun x => f (x (Fin.last k))) ∂μ := by
  change (∫ x, f x ∂((auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ)).map
    (fun x => scalarOpinionClamp (x (Fin.last k))))) = _
  have he := integral_map ((scalarOpinionClamp_continuous.comp (continuous_apply (Fin.last k) : Continuous (fun x : Fin (k+1) → ℝ => x (Fin.last k)))).measurable.aemeasurable)
    (f.continuous.aestronglyMeasurable (μ := ((auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ)).map
      (fun x => scalarOpinionClamp (x (Fin.last k))))))
  simp only [Function.comp_def] at he
  rw [he]
  exact auxiliary_test_integral μ ζ φ hζ hφ c d k (fun x => f (x (Fin.last k)))
    (f.continuous.comp (continuous_apply (Fin.last k)))

theorem native_compact_endpoint_test_integral {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m k : ℕ) (f : C(OpinionInterval, ℝ)) :
    (∫ x, f x ∂(nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k : Measure OpinionInterval)) =
      ∫ ω, f (scalarOpinionClamp (S.R ζ φ c d m k ω (S.I m ω))) ∂P :=
  integral_map (scalarOpinionClamp_continuous.measurable.comp
    (native_root_R_measurable P S 𝓖 ζ φ c d hS m k)).aemeasurable f.continuous.aestronglyMeasurable

theorem native_compact_endpoint_weak_limit {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ) (k : ℕ) :
    Tendsto (fun m => nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k) atTop
      (𝓝 (auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
  intro f
  let fc : C(OpinionInterval, ℝ) := ⟨f, f.continuous⟩
  have h := native_first_test_moment_all_depths P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k
    (fun x => fc (x (Fin.last k))) (fc.continuous.comp (continuous_apply (Fin.last k)))
  change Tendsto (fun m => ∫ x, fc x ∂(nativeCompactEndpointLaw P S 𝓖 ζ φ c d hS m k : Measure OpinionInterval))
    atTop (𝓝 (∫ x, fc x ∂(auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure OpinionInterval)))
  simp_rw [native_compact_endpoint_test_integral, auxiliary_endpoint_test_integral]
  exact h

theorem native_endpoint_empirical_l1 {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ)
    (k : ℕ) (f : C(OpinionInterval, ℝ)) :
    Tendsto (fun m => ∫ ω, |empAvg (fun x => f (scalarOpinionClamp x)) (S.R ζ φ c d m k ω) -
      ∫ x, f x ∂(auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure OpinionInterval)| ∂P)
      atTop (𝓝 0) := by
  rw [auxiliary_endpoint_test_integral]
  exact native_empirical_trajectory_l1 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k
    (fun x => f (x (Fin.last k))) (f.continuous.comp (continuous_apply (Fin.last k)))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem l1_convergence_of_uniform_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (G : ℕ → ℕ → Ω → ℝ) (c : ℝ) (b : ℕ → ℝ)
    (hF : ∀ n, Integrable (F n) P) (hG : ∀ k n, Integrable (G k n) P)
    (hlim : ∀ k, Tendsto (fun n => ∫ ω, |G k n ω-b k| ∂P) atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ k, |b k-c| < δ ∧
      ∀ n, (∫ ω, |F n ω-G k n ω| ∂P) ≤ δ) :
    Tendsto (fun n => ∫ ω, |F n ω-c| ∂P) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun _ => abs_nonneg _)
  · intro ε hε
    obtain ⟨k, hk, hbound⟩ := happrox (ε/3) (by positivity)
    filter_upwards [(hlim k).eventually (gt_mem_nhds (by positivity : 0 < ε/3))] with n hn
    have hi := integral_mono ((hF n).sub (integrable_const c)).abs
      (((hF n).sub (hG k n)).abs.add (((hG k n).sub (integrable_const (b k))).abs.add
        (integrable_const |b k-c|))) (fun ω =>
          (abs_sub_le (F n ω) (G k n ω) c).trans
            (add_le_add le_rfl (abs_sub_le (G k n ω) (b k) c)))
    simp only [Pi.add_apply, Pi.sub_apply] at hi
    have he1 := integral_add ((hF n).sub (hG k n)).abs
      (((hG k n).sub (integrable_const (b k))).abs.add (integrable_const |b k-c|))
    have he2 := integral_add ((hG k n).sub (integrable_const (b k))).abs (integrable_const |b k-c|)
    simp only [Pi.add_apply, Pi.sub_apply] at he1 he2
    rw [he1, he2] at hi
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hi
    linarith [hbound n]

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

theorem integral_abs_eq_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (hmap : P.map F = P.map G) (b : ℝ) :
    (∫ ω, |F ω-b| ∂P) = ∫ ω, |G ω-b| ∂P := by
  have hab : Continuous (fun x : ℝ => |x-b|) := (continuous_id.sub continuous_const).abs
  rw [← integral_map hF.aemeasurable hab.aestronglyMeasurable, hmap,
    integral_map hG.aemeasurable hab.aestronglyMeasurable]

theorem native_stationary_empirical_l1_transfer {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (f : C(OpinionInterval, ℝ))
    (b : ℕ → ℝ) (bLimit : ℝ) (hb : Tendsto b atTop (𝓝 bLimit))
    (hfinite : ∀ k, Tendsto (fun m => ∫ ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.R ζ φ c d m k ω)-b k| ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)-bLimit| ∂P)
      atTop (𝓝 0) := by
  let fr : ℝ → ℝ := fun x => f (scalarOpinionClamp x)
  have hfr : Continuous fr := f.continuous.comp scalarOpinionClamp_continuous
  let F := fun m ω => empAvg fr (S.Rstat ζ c d m ω)
  let G := fun k m ω => empAvg fr (fun i => nativeKernelOpinion ζ φ c d (S.graphData m ω)
    (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i)
  obtain ⟨B, _hB, hfb⟩ := compact_test_bound f f.continuous
  have hbound : ∀ {m} (x : Fin (m+1) → ℝ), |empAvg fr x| ≤ B := by
    intro m x
    unfold empAvg
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/((m:ℝ)+1))]
    calc
      _ ≤ (1/((m:ℝ)+1)) * ∑ _ : Fin (m+1), B :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hfb (scalarOpinionClamp (x i)))) (by positivity)
      _ = B := by simp; field_simp
  have hFm : ∀ m, Measurable (F m) := by
    intro m
    apply measurable_const.mul
    exact Finset.measurable_sum _ (fun i _ => hfr.measurable.comp
      (native_Rstat_measurable P S 𝓖 ζ φ c d hS m i))
  have hGm : ∀ k m, Measurable (G k m) := by
    intro k m
    have hg : Measurable (S.graphData m) := (hS.measurable_graph m).mono (hS.le m) le_rfl
    have hu : Measurable (fun ω p => S.unif m (reverseNoiseIndex m k p) ω) :=
      measurable_pi_lambda _ (fun p => hS.measurable_unif m (reverseNoiseIndex m k p))
    apply measurable_const.mul
    exact Finset.measurable_sum _ (fun i _ => hfr.measurable.comp
      ((nativeKernelOpinion_measurable m ζ φ hS.measurable_ζ hS.measurable_φ c d k i).comp (hg.prodMk hu)))
  have hFi : ∀ m, Integrable (F m) P := fun m => Integrable.of_bound (hFm m).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound (S.Rstat ζ c d m ω))
  have hGi : ∀ k m, Integrable (G k m) P := fun k m => Integrable.of_bound (hGm k m).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using (hbound
      (fun i => nativeKernelOpinion ζ φ c d (S.graphData m ω)
        (fun p => S.unif m (reverseNoiseIndex m k p) ω) k i)))
  apply l1_convergence_of_uniform_approximation P F G bLimit b hFi hGi
  · intro k
    have he : ∀ m, (∫ ω, |G k m ω-b k| ∂P) =
        ∫ ω, |empAvg fr (S.R ζ φ c d m k ω)-b k| ∂P := by
      intro m
      apply integral_abs_eq_of_map_eq P _ _ (hGm k m)
      · apply measurable_const.mul
        exact Finset.measurable_sum _ (fun i _ => hfr.measurable.comp
          (native_R_measurable P S 𝓖 ζ φ c d hS m k i))
      · exact native_empirical_reversed_map P S 𝓖 ζ φ c d hS m k fr hfr.measurable
    simpa only [he] using hfinite k
  · intro δ hδ
    obtain ⟨C, hC, happrox⟩ := native_empirical_stationary_approximation P S 𝓖 ζ φ c d hS f
      (by positivity : 0 < δ/2)
    have hca : Tendsto (fun k : ℕ => C*((1-d)^k*(1+1/d))) atTop (𝓝 0) := by
      simpa using (stationary_rate_tendsto_zero hS.d_pos hS.d_le_one).const_mul C
    obtain ⟨k, hkb, hka⟩ := ((Metric.tendsto_nhds.1 hb δ hδ).and
      (hca.eventually (gt_mem_nhds (by positivity : 0 < δ/2)))).exists
    refine ⟨k, by simpa only [Real.dist_eq] using hkb, ?_⟩
    intro m
    have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg (F m ω-G k m ω))
      (integrable_const (μ := P) (δ/2+C*((1-d)^k*(1+1/d))))
      (Filter.Eventually.of_forall fun ω => happrox m k ω)
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hi
    exact hi.trans (by linarith)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Filter Topology

theorem native_stationary_all_tests {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ) :
    ∃ Lstar : ProbabilityMeasure OpinionInterval,
      (∀ k, ∃ π : ProbabilityMeasure (OpinionInterval × OpinionInterval),
        IsCoupling (π : Measure (OpinionInterval × OpinionInterval))
          (auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k : Measure OpinionInterval)
          (Lstar : Measure OpinionInterval) ∧
        (∫ z, dist z.1 z.2 ∂(π : Measure (OpinionInterval × OpinionInterval))) ≤ (1-d)^k*(1+1/d)) ∧
      ∀ f : C(OpinionInterval, ℝ), Tendsto (fun m => ∫ ω,
        |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω) -
          ∫ x, f x ∂(Lstar : Measure OpinionInterval)| ∂P) atTop (𝓝 0) := by
  let L := auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d
  obtain ⟨Lstar, _hstat, hL, hcoupling⟩ := native_stationary_limit_package P S 𝓖 ζ φ c d hS L
    (native_compact_endpoint_weak_limit P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC)
  refine ⟨Lstar, hcoupling, ?_⟩
  intro f
  exact native_stationary_empirical_l1_transfer P S 𝓖 ζ φ c d hS f
    (fun k => ∫ x, f x ∂(L k : Measure OpinionInterval)) (∫ x, f x ∂(Lstar : Measure OpinionInterval))
    ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto Lstar |>.comp hL)
    (fun k => native_endpoint_empirical_l1 P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC k f)

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Finset Filter Topology

noncomputable def nativeKernelStationary {A : Type*} {m : ℕ} (ζ : Mark A → ℝ → ℝ) (c d : ℝ)
    (z : NativeGraphData A m) (u : Option ℕ × Fin (m+1) → ℝ) (i : Fin (m+1)) : ℝ :=
  liminf (fun n => ∑ r ∈ range n, (Δ (decodeNativeGraph z) c d)^[r]
    (fun j => ζ (decodeNativeMark z j) (u (some r,j))) i) atTop

theorem nativeKernelStationary_measurable {A : Type*} [MeasurableSpace A]
    (m : ℕ) (ζ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (c d : ℝ) (i : Fin (m+1)) :
    Measurable (fun p : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ) =>
      nativeKernelStationary ζ c d p.1 p.2 i) := by
  apply Measurable.liminf
  intro n
  apply Finset.measurable_sum
  intro r _
  apply delta_iterate_measurable
  · intro j; exact measurable_fst.fst.eval
  · intro j t; exact measurable_fst.snd.fst.eval.eval
  · intro j t; exact measurable_fst.snd.snd.fst.eval.eval
  · intro j
    exact hζ.comp (((decodeNativeMark_measurable m j).comp measurable_fst).prodMk (by fun_prop))

theorem nativeKernelStationary_actual {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω)
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ) (ω : Ω) (i : Fin (m+1)) :
    nativeKernelStationary ζ c d (S.graphData m ω) (fun p => S.unif m p ω) i =
      S.Rstat ζ c d m ω i := by
  exact (stationary_summable (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
    hS.d_le_one (fun r j => S.W ζ m r j ω) (fun r j => hS.signal_bound m r j ω) i).hasSum.tendsto_sum_nat.liminf_eq

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem native_stationary_conditional_identity {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ)
    (f : C(OpinionInterval, ℝ)) :
    (fun ω => ∫ x, f (scalarOpinionClamp x) ∂statCondLaw P S ζ c d m ω) =ᵐ[P]
    P[(fun ω => empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)) | S.𝓐 m] := by
  let K := fun i (p : NativeGraphData A m × (Option ℕ × Fin (m+1) → ℝ)) =>
    nativeKernelStationary ζ c d p.1 p.2 i
  have hK : ∀ i, Measurable (K i) := fun i => nativeKernelStationary_measurable m ζ hS.measurable_ζ c d i
  let g := fun x => f (scalarOpinionClamp x)
  have hg : Measurable g := f.continuous.measurable.comp scalarOpinionClamp_continuous.measurable
  let D := fun ω => (S.graphData m ω, fun p => S.unif m p ω)
  have hD : Measurable D := ((hS.measurable_graph m).mono (hS.le m) le_rfl).prodMk
    (measurable_pi_lambda _ (hS.measurable_unif m))
  obtain ⟨B, _hB, hb⟩ := compact_test_bound f f.continuous
  have hi : ∀ i, Integrable (fun ω => g (K i (D ω))) P := fun i =>
    Integrable.of_bound (hg.comp ((hK i).comp hD)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, g] using hb _)
  have hsel : Measurable (fun ω => K (S.I m ω) (D ω)) :=
    measurable_countable_choice (fun i ω => K i (D ω)) (fun i => (hK i).comp hD)
      (S.I m) ((hS.measurable_I m).mono (hS.le m) le_rfl)
  have hri : Integrable (fun ω => g (K (S.I m ω) (D ω))) P :=
    Integrable.of_bound (hg.comp hsel).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, g] using hb _)
  have hid := native_conditional_kernel_test_identity P S 𝓖 ζ φ c d hS m K hK g hg.stronglyMeasurable hi hri
  have he : ∀ i ω, K i (S.graphData m ω, fun p => S.unif m p ω) = S.Rstat ζ c d m ω i :=
    fun i ω => nativeKernelStationary_actual P S 𝓖 ζ φ c d hS m ω i
  simpa only [he, g, statCondLaw, empAvg, Fintype.card_fin, Nat.cast_add, Nat.cast_one, one_div] using hid

noncomputable def nativeStationaryCondProbability {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] (P : Measure Ω) [IsFiniteMeasure P] (S : GraphSeq Ω A)
    (ζ : Mark A → ℝ → ℝ) (c d : ℝ) (m : ℕ) (ω : Ω) : ProbabilityMeasure ℝ :=
  ⟨statCondLaw P S ζ c d m ω, by unfold statCondLaw; infer_instance⟩

theorem native_stationary_cond_support {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (m : ℕ) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂statCondLaw P S ζ c d m ω, x ∈ Icc (-1:ℝ) 1 := by
  apply conditional_law_support P (S.attrs m) (fun ω => S.Rstat ζ c d m ω (S.I m ω))
    ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl).aemeasurable
    (native_root_Rstat_measurable P S 𝓖 ζ φ c d hS m).aemeasurable
    (fun x => x ∈ Icc (-1:ℝ) 1) isClosed_Icc.measurableSet
  exact Filter.Eventually.of_forall fun ω => abs_le.mp
    (stationary_abs_le_one (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
      hS.d_le_one (fun t j => S.W ζ m t j ω) (fun t j => hS.signal_bound m t j ω) (S.I m ω))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem scalar_compact_coupling_transport_bound
    (μ ν : ProbabilityMeasure OpinionInterval) (π : ProbabilityMeasure (OpinionInterval × OpinionInterval))
    (hπ : IsCoupling (π : Measure (OpinionInterval × OpinionInterval))
      (μ : Measure OpinionInterval) (ν : Measure OpinionInterval)) (a : ℝ)
    (hc : (∫ z, dist z.1 z.2 ∂(π : Measure (OpinionInterval × OpinionInterval))) ≤ a) :
    W1 ((μ : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ))
      ((ν : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ)) ≤ ENNReal.ofReal a := by
  have hm := transport_map_le (fun x y : OpinionInterval => ENNReal.ofReal (dist x y))
    (fun x y : ℝ => ENNReal.ofReal |x-y|)
    (by exact ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).abs))
    (μ : Measure OpinionInterval) (ν : Measure OpinionInterval)
    measurable_subtype_coe measurable_subtype_coe (fun _ _ => le_rfl)
  have hd : Integrable (fun z : OpinionInterval × OpinionInterval => dist z.1 z.2)
      (π : Measure (OpinionInterval × OpinionInterval)) :=
    continuous_dist.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ht := transport_le_coupling (fun x y : OpinionInterval => ENNReal.ofReal (dist x y)) hπ
  have he := ofReal_integral_eq_lintegral_ofReal hd
    (Filter.Eventually.of_forall fun z : OpinionInterval × OpinionInterval => dist_nonneg (x := z.1) (y := z.2))
  exact hm.trans (ht.trans (he.symm.le.trans (ENNReal.ofReal_le_ofReal hc)))

theorem scalar_compact_transport_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ℕ → Ω → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hμ : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ n ω : Measure ℝ), x ∈ Icc (-1:ℝ) 1)
    (hν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (-1:ℝ) 1)
    (htest : ∀ f : C(OpinionInterval, ℝ), TendstoInMeasure P
      (fun n ω => ∫ x, f (scalarOpinionClamp x) ∂(μ n ω : Measure ℝ)) atTop
      (fun _ => ∫ x, f (scalarOpinionClamp x) ∂(ν : Measure ℝ)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε ≤ W1 (μ n ω : Measure ℝ) (ν : Measure ℝ)})
      atTop (𝓝 0) := by
  have hfixμ : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ x ∂(μ n ω : Measure ℝ),
      (scalarOpinionClamp x : ℝ) = x := by
    intro n
    filter_upwards [hμ n] with ω hω
    filter_upwards [hω] with x hx
    exact scalarOpinionClamp_eq x hx
  have hfixν : ∀ᵐ x ∂(ν : Measure ℝ), (scalarOpinionClamp x : ℝ) = x := by
    filter_upwards [hν] with x hx
    exact scalarOpinionClamp_eq x hx
  have hdiam : ∀ x y : OpinionInterval, dist x y ≤ 2 := by
    intro x y
    change |(x:ℝ)-(y:ℝ)| ≤ 2
    exact abs_le.mpr ⟨by linarith [x.property.1, y.property.2], by linarith [x.property.2, y.property.1]⟩
  simpa only [W1, Real.dist_eq] using compact_retraction_transport_in_probability P μ ν
    scalarOpinionClamp ((↑) : OpinionInterval → ℝ) scalarOpinionClamp_continuous continuous_subtype_val
    (fun _ _ => le_rfl) hfixμ hfixν htest 2 (by norm_num) hdiam ε hε

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set

noncomputable def embedOpinionLaw (L : ProbabilityMeasure OpinionInterval) : ProbabilityMeasure ℝ :=
  L.map measurable_subtype_coe.aemeasurable

theorem embedOpinionLaw_supported (L : ProbabilityMeasure OpinionInterval) :
    ∀ᵐ x ∂(embedOpinionLaw L : Measure ℝ), x ∈ Icc (-1:ℝ) 1 := by
  exact (ae_map_iff measurable_subtype_coe.aemeasurable isClosed_Icc.measurableSet).2
    (Filter.Eventually.of_forall fun x : OpinionInterval => x.property)

theorem scalarOpinionClamp_coe (x : OpinionInterval) : scalarOpinionClamp (x : ℝ) = x :=
  Subtype.ext (clip_eq x.property)

theorem embedOpinionLaw_test_integral (L : ProbabilityMeasure OpinionInterval) (f : C(OpinionInterval, ℝ)) :
    (∫ y, f (scalarOpinionClamp y) ∂(embedOpinionLaw L : Measure ℝ)) =
      ∫ x, f x ∂(L : Measure OpinionInterval) := by
  rw [show (embedOpinionLaw L : Measure ℝ) = (L : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ) from rfl]
  have htest : AEStronglyMeasurable (fun y : ℝ => f (scalarOpinionClamp y))
      ((L : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ)) :=
    (f.continuous.comp scalarOpinionClamp_continuous).aestronglyMeasurable
  rw [integral_map measurable_subtype_coe.aemeasurable htest]
  simp only [scalarOpinionClamp_coe]

theorem embedOpinionLaw_continuousOn_integral (L : ProbabilityMeasure OpinionInterval)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    (∫ y, f y ∂(embedOpinionLaw L : Measure ℝ)) = ∫ x : OpinionInterval, f x ∂(L : Measure OpinionInterval) := by
  rw [continuousOn_supported_integral hf _ (embedOpinionLaw_supported L)]
  change (∫ y, extendTest f y ∂(L : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ)) = _
  rw [integral_map measurable_subtype_coe.aemeasurable (extendTest_continuous hf).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x : OpinionInterval => extendTest_eq x.property)

theorem auxiliary_compact_endpoint_embedding {A : Type*} [MeasurableSpace A]
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ]
    (ζ φ : Mark A → ℝ → ℝ) (hζ : Measurable (Function.uncurry ζ))
    (hφ : Measurable (Function.uncurry φ)) (c d : ℝ) (k : ℕ) :
    (auxiliaryCompactEndpointLaw μ ζ φ hζ hφ c d k : Measure OpinionInterval).map ((↑) : OpinionInterval → ℝ) =
      (auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ)).map
        (fun x => x (Fin.last k)) := by
  change ((auxiliaryTrajectoryLaw μ ζ φ hζ hφ c d k : Measure (Fin (k+1) → ℝ)).map
    (fun x => scalarOpinionClamp (x (Fin.last k)))).map ((↑) : OpinionInterval → ℝ) = _
  have hm : Measurable (fun x : Fin (k+1) → ℝ => scalarOpinionClamp (x (Fin.last k))) :=
    (scalarOpinionClamp_continuous.comp (continuous_apply (Fin.last k))).measurable
  rw [Measure.map_map measurable_subtype_coe hm]
  apply Measure.map_congr
  filter_upwards [auxiliaryTrajectoryLaw_supported μ ζ φ hζ hφ c d k] with x hx
  exact scalarOpinionClamp_eq _ (hx (Fin.last k))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [PseudoMetricSpace A] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
variable (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
variable (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
include hS

theorem native_stationary_empirical_integrable (f : C(OpinionInterval, ℝ)) (m : ℕ) :
    Integrable (fun ω => empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)) P := by
  obtain ⟨B, _hB, hb⟩ := compact_test_bound f f.continuous
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  apply Integrable.of_bound
    ((f.continuous.comp scalarOpinionClamp_continuous).measurable.comp
      (native_Rstat_measurable P S 𝓖 ζ φ c d hS m i)).aestronglyMeasurable B
  exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb _

theorem native_stationary_conditional_test (L : ProbabilityMeasure OpinionInterval)
    (f : C(OpinionInterval, ℝ))
    (hL1 : Tendsto (fun m => ∫ ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)-∫ x, f x ∂(L : Measure OpinionInterval)| ∂P)
      atTop (𝓝 0)) :
    TendstoInMeasure P (fun m ω => ∫ x, f (scalarOpinionClamp x) ∂statCondLaw P S ζ c d m ω)
      atTop (fun _ => ∫ x, f (scalarOpinionClamp x) ∂(embedOpinionLaw L : Measure ℝ)) := by
  rw [embedOpinionLaw_test_integral]
  apply conditional_test_in_measure_of_ae_eq P S.𝓐
    (fun m => ((hS.measurable_graph m).snd.snd.snd.mono (hS.le m) le_rfl).comap_le)
    (fun m ω => empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)) _
    (native_stationary_empirical_integrable P S 𝓖 ζ φ c d hS f)
  · intro m
    exact native_stationary_conditional_identity P S 𝓖 ζ φ c d hS m f
  · exact hL1

theorem native_stationary_conditional_W1 (L : ProbabilityMeasure OpinionInterval)
    (hL1 : ∀ f : C(OpinionInterval, ℝ), Tendsto (fun m => ∫ ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)-∫ x, f x ∂(L : Measure OpinionInterval)| ∂P)
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => P {ω | ENNReal.ofReal ε ≤ W1 (statCondLaw P S ζ c d m ω)
      (embedOpinionLaw L : Measure ℝ)}) atTop (𝓝 0) := by
  apply scalar_compact_transport_in_probability P (nativeStationaryCondProbability P S ζ c d)
    (embedOpinionLaw L)
  · exact native_stationary_cond_support P S 𝓖 ζ φ c d hS
  · exact embedOpinionLaw_supported L
  · intro f
    exact native_stationary_conditional_test P S 𝓖 ζ φ c d hS L f (hL1 f)
  · exact hε

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_stationary_empirical_scalar {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d) (L : ProbabilityMeasure OpinionInterval)
    (hL1 : ∀ f : C(OpinionInterval, ℝ), Tendsto (fun m => ∫ ω,
      |empAvg (fun x => f (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)-∫ x, f x ∂(L : Measure OpinionInterval)| ∂P)
      atTop (𝓝 0)) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (-1:ℝ) 1)) :
    TendstoInMeasure P (fun m ω => empAvg f (S.Rstat ζ c d m ω)) atTop
      (fun _ => ∫ x, f x ∂(embedOpinionLaw L : Measure ℝ)) := by
  let fc : C(OpinionInterval, ℝ) := ⟨fun x => extendTest f x,
    (extendTest_continuous hf).comp continuous_subtype_val⟩
  have ha : (fun m ω => empAvg (fun x => fc (scalarOpinionClamp x)) (S.Rstat ζ c d m ω)) =
      (fun m ω => empAvg f (S.Rstat ζ c d m ω)) := by
    funext m ω
    unfold empAvg
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hx : S.Rstat ζ c d m ω i ∈ Icc (-1:ℝ) 1 := abs_le.mp
      (stationary_abs_le_one (S.G m ω) (hS.valid m ω) hS.c_nonneg hS.cd_le_one hS.d_pos
        hS.d_le_one (fun t j => S.W ζ m t j ω) (fun t j => hS.signal_bound m t j ω) i)
    change extendTest f (scalarOpinionClamp (S.Rstat ζ c d m ω i)) = _
    rw [scalarOpinionClamp_eq _ hx, extendTest_eq hx]
  have hi : (∫ x, fc x ∂(L : Measure OpinionInterval)) = ∫ x, f x ∂(embedOpinionLaw L : Measure ℝ) := by
    rw [embedOpinionLaw_continuousOn_integral L f hf]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x : OpinionInterval => extendTest_eq x.property)
  have ht := in_measure_of_integral_abs_sub_const P
    (fun m ω => empAvg (fun x => fc (scalarOpinionClamp x)) (S.Rstat ζ c d m ω))
    (native_stationary_empirical_integrable P S 𝓖 ζ φ c d hS fc) _ (hL1 fc)
  rw [ha, hi] at ht
  exact ht

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical.OpinionFresh
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem native_stationary_branch {Ω A : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace A] [MeasurableSpace A] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : GraphSeq Ω A) (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ)
    (c d K : ℝ) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hKζ : KernelLipschitz ζ K) (hKφ : KernelLipschitz φ K)
    (μ : Measure (LimGraph A)) [IsProbabilityMeasure μ] (hSC : StrongCoupling P S 𝓖 μ) :
    ∃ Lstar : ProbabilityMeasure ℝ,
      ((∀ ε : ℝ, 0 < ε → Tendsto (fun m => P {ω | ENNReal.ofReal ε ≤
        W1 (statCondLaw P S ζ c d m ω) (Lstar : Measure ℝ)}) atTop (𝓝 0)) ∧
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1:ℝ) 1) →
        TendstoInMeasure P (fun m ω => empAvg f (S.Rstat ζ c d m ω)) atTop
          (fun _ => ∫ x, f x ∂(Lstar : Measure ℝ)))) ∧
      ∀ k, W1 ((auxiliaryTrajectoryLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k :
        Measure (Fin (k+1) → ℝ)).map (fun x => x (Fin.last k))) (Lstar : Measure ℝ) ≤
          ENNReal.ofReal ((1-d)^k*(2/d+2)) := by
  obtain ⟨L, hcoupling, hL1⟩ := native_stationary_all_tests P S 𝓖 ζ φ c d K hS hKζ hKφ μ hSC
  refine ⟨embedOpinionLaw L, ⟨?_, ?_⟩, ?_⟩
  · intro ε hε
    exact native_stationary_conditional_W1 P S 𝓖 ζ φ c d hS L hL1 ε hε
  · intro f hf
    exact native_stationary_empirical_scalar P S 𝓖 ζ φ c d hS L hL1 f hf
  · intro k
    obtain ⟨π, hπ, hc⟩ := hcoupling k
    have hb := scalar_compact_coupling_transport_bound
      (auxiliaryCompactEndpointLaw μ ζ φ hS.measurable_ζ hS.measurable_φ c d k) L π hπ _ hc
    rw [auxiliary_compact_endpoint_embedding] at hb
    exact hb.trans (ENNReal.ofReal_le_ofReal (stationary_rate_le_native_rate hS.d_pos hS.d_le_one k))

end DirectedOpinion.Typical.OpinionFresh
end

section
namespace DirectedOpinion.Typical

open MeasureTheory ProbabilityTheory Set Filter Topology
open OpinionFresh

theorem theorem_2 {Ω A : Type*} [MeasurableSpace Ω] [MetricSpace A] [MeasurableSpace A]
    [BorelSpace A] [PolishSpace A] (P : Measure Ω) [IsProbabilityMeasure P] (S : GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : Mark A → ℝ → ℝ) (c d K : ℝ)
    (μlim : Measure (LimGraph A)) (hS : GraphSeqModel P S 𝓖 ζ φ c d)
    (hSC : StrongCoupling P S 𝓖 μlim) (hd : 0 < d) (hK : KernelLipschitz ζ K)
    (hK0 : KernelLipschitz φ K) :
    ∃ (L : (k : ℕ) → ProbabilityMeasure (Fin (k + 1) → ℝ)) (Lstar : ProbabilityMeasure ℝ),
      (∀ k : ℕ,
        (∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              W1vec (trajCondLaw P S ζ φ c d m k ω) (L k : Measure (Fin (k + 1) → ℝ))})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => empAvg f (S.R ζ φ c d m k ω)) atTop
            (fun _ => ∫ y, f (y (Fin.last k)) ∂(L k : Measure (Fin (k + 1) → ℝ)))) ∧
      ((∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              W1 (statCondLaw P S ζ c d m ω) (Lstar : Measure ℝ)})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => empAvg f (S.Rstat ζ c d m ω)) atTop
            (fun _ => ∫ y, f y ∂(Lstar : Measure ℝ))) ∧
      ∀ k : ℕ,
        W1 ((L k : Measure (Fin (k + 1) → ℝ)).map (fun y => y (Fin.last k))) (Lstar : Measure ℝ) ≤
          ENNReal.ofReal ((1 - d) ^ k * (2 / d + 2)) := by
  let : IsProbabilityMeasure μlim := strongCoupling_limit_probability P S 𝓖 μlim hSC
  let hS' : GraphSeqModel P S 𝓖 ζ φ c d := { hS with d_pos := hd }
  obtain ⟨Lstar,hstat,hrate⟩ := native_stationary_branch P S 𝓖 ζ φ c d K hS' hK hK0 μlim hSC
  refine ⟨auxiliaryTrajectoryLaw μlim ζ φ hS'.measurable_ζ hS'.measurable_φ c d,Lstar,?_,hstat,hrate⟩
  exact native_finite_branch P S 𝓖 ζ φ c d K hS' hK hK0 μlim hSC

end DirectedOpinion.Typical
end

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem solution {Ω A : Type*} [MeasurableSpace Ω] [MetricSpace A] [MeasurableSpace A]
    [BorelSpace A] [PolishSpace A] (P : Measure Ω) [IsProbabilityMeasure P] (S : DirectedOpinion.Typical.GraphSeq Ω A)
    (𝓖 : ℕ → MeasurableSpace Ω) (ζ φ : DirectedOpinion.Typical.Mark A → ℝ → ℝ) (c d K : ℝ)
    (μlim : Measure (DirectedOpinion.Typical.LimGraph A)) (hS : DirectedOpinion.Typical.GraphSeqModel P S 𝓖 ζ φ c d)
    (hSC : DirectedOpinion.Typical.StrongCoupling P S 𝓖 μlim) (hd : 0 < d) (hK : DirectedOpinion.Typical.KernelLipschitz ζ K)
    (hK0 : DirectedOpinion.Typical.KernelLipschitz φ K) :
    ∃ (L : (k : ℕ) → ProbabilityMeasure (Fin (k + 1) → ℝ)) (Lstar : ProbabilityMeasure ℝ),
      (∀ k : ℕ,
        (∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              DirectedOpinion.Typical.W1vec (DirectedOpinion.Typical.trajCondLaw P S ζ φ c d m k ω) (L k : Measure (Fin (k + 1) → ℝ))})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => DirectedOpinion.Typical.empAvg f (S.R ζ φ c d m k ω)) atTop
            (fun _ => ∫ y, f (y (Fin.last k)) ∂(L k : Measure (Fin (k + 1) → ℝ)))) ∧
      ((∀ η : ℝ, 0 < η →
          Tendsto (fun m => P {ω | ENNReal.ofReal η ≤
              DirectedOpinion.Typical.W1 (DirectedOpinion.Typical.statCondLaw P S ζ c d m ω) (Lstar : Measure ℝ)})
            atTop (𝓝 0)) ∧
        ∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          TendstoInMeasure P (fun m ω => DirectedOpinion.Typical.empAvg f (S.Rstat ζ c d m ω)) atTop
            (fun _ => ∫ y, f y ∂(Lstar : Measure ℝ))) ∧
      ∀ k : ℕ,
        DirectedOpinion.Typical.W1 ((L k : Measure (Fin (k + 1) → ℝ)).map (fun y => y (Fin.last k))) (Lstar : Measure ℝ) ≤
          ENNReal.ofReal ((1 - d) ^ k * (2 / d + 2)) := by
  exact DirectedOpinion.Typical.theorem_2 P S 𝓖 ζ φ c d K μlim hS hSC hd hK hK0
