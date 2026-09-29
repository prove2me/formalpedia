-- Prove2me | solution 1 for EthierKurtz.exclusion_feller_generation
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T19:00:15.812466+00:00
-- url     : https://prove2.me/submissions/702e23bc-3a00-48f9-8ffa-21e0e40225d7

import Theorems.Thm_EthierKurtz_feller_generation_of_positive_maximum
import Theorems.Thm_EthierKurtz_exclusion_cylinder_range_dense

open Filter
open scoped Topology BigOperators

namespace EthierKurtz.ExclusionReduction

open EthierKurtz

section General

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The positive maximum principle implies dissipativity. -/
theorem dissipative_of_pmp (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (r : ℝ) : ∀ p ∈ G, r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖ := by
  intro p hp
  rcases isEmpty_or_nonempty X with hX | hX
  · have : p.1 = 0 := Subsingleton.elim _ _
    simp [this]
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp p.1.continuous).continuousOn
  have hnorm : ‖p.1‖ = |p.1 x| :=
    le_antisymm ((ContinuousMap.norm_le _ (abs_nonneg _)).2 fun y => hx (Set.mem_univ y))
      (p.1.norm_coe_le_norm x)
  have key : ∀ q ∈ G, q.1 x = ‖q.1‖ → r * ‖q.1‖ ≤ ‖r • q.1 - q.2‖ := by
    intro q hq hqx
    have hmax : ∀ y, q.1 y ≤ q.1 x := fun y => hqx ▸ q.1.apply_le_norm y
    have h2 := hpmp q hq x hmax (hqx ▸ norm_nonneg _)
    calc r * ‖q.1‖ ≤ r * q.1 x - q.2 x := by rw [hqx]; linarith
      _ = (r • q.1 - q.2) x := by simp
      _ ≤ ‖r • q.1 - q.2‖ := ContinuousMap.apply_le_norm _ _
  rcases le_or_gt 0 (p.1 x) with h | h
  · exact key p hp (by rw [hnorm, abs_of_nonneg h])
  · have := key (-p) (G.neg_mem hp) (by simp [hnorm, abs_of_neg h])
    have e : r • (-p).1 - (-p).2 = -(r • p.1 - p.2) := by simp [smul_neg]; abel
    rw [e, norm_neg] at this
    simpa using this

/-- The positive maximum principle implies dissipativity on the closure. -/
theorem dissipative_closure_of_pmp (G : Submodule ℝ (C(X, ℝ) × C(X, ℝ)))
    (hpmp : ∀ fg ∈ G, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0)
    (r : ℝ) :
    ∀ p ∈ closure (G : Set (C(X, ℝ) × C(X, ℝ))), r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖ := by
  have hcl : IsClosed {p : C(X, ℝ) × C(X, ℝ) | r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖} :=
    isClosed_le (continuous_const.mul (continuous_norm.comp continuous_fst))
      (continuous_norm.comp ((continuous_fst.const_smul r).sub continuous_snd))
  exact closure_minimal (fun p hp => dissipative_of_pmp G hpmp r p hp) hcl

end General

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If `G' ≤ G`, the closure of `G` is dissipative for `r > 0`, and `r - G'` has dense
range, then `G'` and `G` have the same closure. -/
theorem closure_eq_of_dissipative_of_denseRange (G' G : Submodule ℝ (E × E)) (hle : G' ≤ G)
    (r : ℝ) (hr : 0 < r)
    (hdiss : ∀ p ∈ closure (G : Set (E × E)), r * ‖p.1‖ ≤ ‖r • p.1 - p.2‖)
    (hrange : Dense ((fun fg : E × E => r • fg.1 - fg.2) '' (G' : Set (E × E)))) :
    closure (G' : Set (E × E)) = closure (G : Set (E × E)) := by
  have hsub : closure (G' : Set (E × E)) ⊆ closure (G : Set (E × E)) := closure_mono hle
  refine le_antisymm hsub ?_
  set H := G'.topologicalClosure with hH
  have : CompleteSpace H := (G'.isClosed_topologicalClosure).completeSpace_coe
  let L0 : (E × E) →L[ℝ] E := r • ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E
  let L : H →L[ℝ] E := L0.comp H.subtypeL
  have hL : ∀ p : H, L p = r • (p : E × E).1 - (p : E × E).2 := fun p => rfl
  have hbound : ∀ p : H, ‖p‖ ≤ (1 / r + 2) * ‖L p‖ := by
    intro p
    have hp : (p : E × E) ∈ closure (G : Set (E × E)) := hsub p.2
    have h1 := hdiss _ hp
    rw [← hL] at h1
    have h1' : ‖(p : E × E).1‖ ≤ ‖L p‖ / r := by rw [le_div_iff₀ hr]; linarith
    have h2 : ‖(p : E × E).2‖ ≤ 2 * ‖L p‖ := by
      have : (p : E × E).2 = r • (p : E × E).1 - L p := by rw [hL]; abel
      rw [this]
      calc ‖r • (p : E × E).1 - L p‖ ≤ ‖r • (p : E × E).1‖ + ‖L p‖ := norm_sub_le _ _
        _ = r * ‖(p : E × E).1‖ + ‖L p‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ ≤ 2 * ‖L p‖ := by linarith
    have hn : ‖p‖ = max ‖(p : E × E).1‖ ‖(p : E × E).2‖ := by
      rw [Submodule.coe_norm]; rfl
    rw [hn]
    have hLn := norm_nonneg (L p)
    have : ‖L p‖ / r = (1 / r) * ‖L p‖ := by ring
    refine max_le ?_ ?_
    · nlinarith [one_div_pos.2 hr]
    · nlinarith [one_div_pos.2 hr]
  have hanti : AntilipschitzWith (Real.toNNReal (1 / r + 2)) L :=
    L.antilipschitz_of_bound (fun p => by
      rw [Real.coe_toNNReal _ (by positivity)]; exact hbound p)
  have hclosed : IsClosed (Set.range L) := hanti.isClosed_range L.uniformContinuous
  have hrange' : Set.range L = Set.univ := by
    have hd : Dense (Set.range L) := hrange.mono (by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨⟨q, subset_closure hq⟩, rfl⟩)
    rw [← hclosed.closure_eq, hd.closure_eq]
  intro p hp
  obtain ⟨q, hq⟩ : ∃ q : H, L q = r • p.1 - p.2 := by
    have : r • p.1 - p.2 ∈ Set.range L := by rw [hrange']; trivial
    exact this
  have hd : p - (q : E × E) ∈ closure (G : Set (E × E)) :=
    (G.topologicalClosure.sub_mem hp (hsub q.2) : _)
  have h0 := hdiss _ hd
  have hz : r • (p - (q : E × E)).1 - (p - (q : E × E)).2 = 0 := by
    rw [hL] at hq
    simp only [Prod.fst_sub, Prod.snd_sub, smul_sub]
    have : r • p.1 - r • (q : E × E).1 - (p.2 - (q : E × E).2) =
        (r • p.1 - p.2) - (r • (q : E × E).1 - (q : E × E).2) := by abel
    rw [this, hq, sub_self]
  rw [hz, norm_zero] at h0
  have h1 : (p - (q : E × E)).1 = 0 := by
    have : ‖(p - (q : E × E)).1‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (p - (q : E × E)).1]) (norm_nonneg _)
    exact norm_eq_zero.1 this
  have h2 : (p - (q : E × E)).2 = 0 := by
    have := hz; rw [h1, smul_zero, zero_sub, neg_eq_zero] at this; exact this
  have : p = q := sub_eq_zero.1 (Prod.ext h1 h2)
  rw [this]; exact q.2

end Abstract

section Exclusion

variable {S : Type*}

theorem continuous_exclusionExchange (i j : S) :
    Continuous (exclusionExchange i j : (S → Bool) → S → Bool) := by
  classical
  unfold exclusionExchange
  refine continuous_pi fun k => ?_
  split_ifs <;> exact continuous_apply _

theorem abs_sub_le_two_norm (f : C(S → Bool, ℝ)) (a b : S → Bool) : |f a - f b| ≤ 2 * ‖f‖ := by
  have h1 := f.norm_coe_le_norm a
  have h2 := f.norm_coe_le_norm b
  rw [Real.norm_eq_abs] at h1 h2
  calc |f a - f b| ≤ |f a| + |f b| := abs_sub _ _
    _ ≤ 2 * ‖f‖ := by linarith

theorem bddAbove_range_exchange (f : C(S → Bool, ℝ)) (i j : S) :
    BddAbove (Set.range (fun η : S → Bool => |f (exclusionExchange i j η) - f η|)) :=
  ⟨2 * ‖f‖, by rintro _ ⟨η, rfl⟩; exact abs_sub_le_two_norm f _ _⟩

theorem abs_sub_le_exclusionVariation (f : C(S → Bool, ℝ)) (i j : S) (η : S → Bool) :
    |f (exclusionExchange i j η) - f η| ≤ exclusionVariation f i j :=
  le_csSup (bddAbove_range_exchange f i j) ⟨η, rfl⟩

theorem exclusionVariation_nonneg (f : C(S → Bool, ℝ)) (i j : S) :
    0 ≤ exclusionVariation f i j :=
  (abs_nonneg _).trans (abs_sub_le_exclusionVariation f i j (fun _ => false))

theorem exclusionVariation_le_iff (f : C(S → Bool, ℝ)) (i j : S) (b : ℝ) :
    exclusionVariation f i j ≤ b ↔ ∀ η, |f (exclusionExchange i j η) - f η| ≤ b := by
  refine ⟨fun h η => (abs_sub_le_exclusionVariation f i j η).trans h, fun h => ?_⟩
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨η, rfl⟩; exact h η)

theorem exclusionVariation_add_le (f g : C(S → Bool, ℝ)) (i j : S) :
    exclusionVariation (f + g) i j ≤ exclusionVariation f i j + exclusionVariation g i j := by
  rw [exclusionVariation_le_iff]
  intro η
  have h1 := abs_sub_le_exclusionVariation f i j η
  have h2 := abs_sub_le_exclusionVariation g i j η
  simp only [ContinuousMap.add_apply]
  calc |f (exclusionExchange i j η) + g (exclusionExchange i j η) - (f η + g η)|
      = |(f (exclusionExchange i j η) - f η) + (g (exclusionExchange i j η) - g η)| := by
        ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem exclusionVariation_smul (a : ℝ) (f : C(S → Bool, ℝ)) (i j : S) :
    exclusionVariation (a • f) i j = |a| * exclusionVariation f i j := by
  unfold exclusionVariation
  have : (fun η : S → Bool => |(a • f) (exclusionExchange i j η) - (a • f) η|) =
      fun η => |a| * |f (exclusionExchange i j η) - f η| := by
    funext η; simp [← mul_sub, abs_mul]
  rw [this]
  exact (Real.mul_iSup_of_nonneg (abs_nonneg a) _).symm

theorem exclusionVariation_le_two_norm (f : C(S → Bool, ℝ)) (i j : S) :
    exclusionVariation f i j ≤ 2 * ‖f‖ :=
  (exclusionVariation_le_iff f i j _).2 fun _ => abs_sub_le_two_norm f _ _

variable (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)

theorem norm_exclusion_term_le
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hdom : ∀ i j η, c i j η ≤ γ i j)
    (f : C(S → Bool, ℝ)) (i j : S) (η : S → Bool) :
    ‖c i j η * (f (exclusionExchange i j η) - f η)‖ ≤ γ i j * exclusionVariation f i j := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc_nonneg i j η)]
  exact mul_le_mul (hdom i j η) (abs_sub_le_exclusionVariation f i j η) (abs_nonneg _)
    ((hc_nonneg i j η).trans (hdom i j η))

/-- The pointwise exchange series is summable on the weighted domain. -/
theorem exclusion_series_summable
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hdom : ∀ i j η, c i j η ≤ γ i j)
    (f : C(S → Bool, ℝ))
    (hf : Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2))
    (η : S → Bool) :
    Summable (fun ij : S × S => c ij.1 ij.2 η * (f (exclusionExchange ij.1 ij.2 η) - f η)) :=
  Summable.of_norm_bounded hf fun ij => norm_exclusion_term_le c γ hc_nonneg hdom f ij.1 ij.2 η

/-- The pointwise exchange series is continuous on the weighted domain. -/
theorem exclusion_series_continuous
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hdom : ∀ i j η, c i j η ≤ γ i j)
    (f : C(S → Bool, ℝ))
    (hf : Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2)) :
    Continuous (fun η => ∑' ij : S × S,
      c ij.1 ij.2 η * (f (exclusionExchange ij.1 ij.2 η) - f η)) := by
  refine continuous_tsum (fun ij => ?_) hf
    (fun ij η => norm_exclusion_term_le c γ hc_nonneg hdom f ij.1 ij.2 η)
  exact (c ij.1 ij.2).continuous.mul
    ((f.continuous.comp (continuous_exclusionExchange ij.1 ij.2)).sub f.continuous)

theorem exists_mem_exclusionGraph
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hdom : ∀ i j η, c i j η ≤ γ i j)
    (f : C(S → Bool, ℝ))
    (hf : Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2)) :
    ∃ g, (f, g) ∈ exclusionGraph c γ :=
  ⟨⟨_, exclusion_series_continuous c γ hc_nonneg hdom f hf⟩, hf, fun _ => rfl⟩

theorem exclusionGraph_zero_mem :
    ((0 : C(S → Bool, ℝ)), (0 : C(S → Bool, ℝ))) ∈ exclusionGraph c γ := by
  have h0 : ∀ i j, exclusionVariation (0 : C(S → Bool, ℝ)) i j = 0 := fun i j => by
    have := exclusionVariation_smul (0 : ℝ) (0 : C(S → Bool, ℝ)) i j
    simpa using this
  refine ⟨?_, fun η => ?_⟩
  · simp only [h0, mul_zero]; exact summable_zero
  · simp

theorem exclusionGraph_add_mem
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdom : ∀ i j η, c i j η ≤ γ i j)
    {p q : C(S → Bool, ℝ) × C(S → Bool, ℝ)} (hp : p ∈ exclusionGraph c γ)
    (hq : q ∈ exclusionGraph c γ) : p + q ∈ exclusionGraph c γ := by
  refine ⟨?_, fun η => ?_⟩
  · refine Summable.of_nonneg_of_le (fun ij => mul_nonneg (hγ_nonneg _ _)
      (exclusionVariation_nonneg _ _ _)) (fun ij => ?_) (hp.1.add hq.1)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (exclusionVariation_add_le _ _ _ _) (hγ_nonneg _ _)
  · simp only [Prod.fst_add, Prod.snd_add, ContinuousMap.add_apply]
    rw [hp.2 η, hq.2 η, ← (exclusion_series_summable c γ hc_nonneg hdom _ hp.1 η).tsum_add
      (exclusion_series_summable c γ hc_nonneg hdom _ hq.1 η)]
    congr 1; funext ij; ring

theorem exclusionGraph_smul_mem (a : ℝ)
    {p : C(S → Bool, ℝ) × C(S → Bool, ℝ)} (hp : p ∈ exclusionGraph c γ) :
    a • p ∈ exclusionGraph c γ := by
  refine ⟨?_, fun η => ?_⟩
  · simp only [Prod.smul_fst, exclusionVariation_smul]
    have := hp.1.mul_left |a|
    refine this.congr fun ij => ?_
    ring
  · simp only [Prod.smul_fst, Prod.smul_snd, ContinuousMap.smul_apply, smul_eq_mul]
    rw [hp.2 η, ← tsum_mul_left]
    congr 1; funext ij; ring

/-- The exclusion graph as a submodule. -/
noncomputable def exclusionSubmodule
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdom : ∀ i j η, c i j η ≤ γ i j) :
    Submodule ℝ (C(S → Bool, ℝ) × C(S → Bool, ℝ)) where
  carrier := exclusionGraph c γ
  add_mem' hp hq := exclusionGraph_add_mem c γ hc_nonneg hγ_nonneg hdom hp hq
  zero_mem' := exclusionGraph_zero_mem c γ
  smul_mem' a _ hp := exclusionGraph_smul_mem c γ a hp

/-- A function depending only on finitely many coordinates. -/
def IsCylinder (f : C(S → Bool, ℝ)) : Prop :=
  ∃ F : Finset S, ∀ η ξ : S → Bool, (∀ i ∈ F, η i = ξ i) → f η = f ξ

theorem IsCylinder.add {f g : C(S → Bool, ℝ)} (hf : IsCylinder f) (hg : IsCylinder g) :
    IsCylinder (f + g) := by
  classical
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨F ∪ G, fun η ξ h => ?_⟩
  simp only [ContinuousMap.add_apply]
  rw [hF η ξ (fun i hi => h i (Finset.mem_union_left _ hi)),
    hG η ξ (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem IsCylinder.mul {f g : C(S → Bool, ℝ)} (hf : IsCylinder f) (hg : IsCylinder g) :
    IsCylinder (f * g) := by
  classical
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨F ∪ G, fun η ξ h => ?_⟩
  simp only [ContinuousMap.mul_apply]
  rw [hF η ξ (fun i hi => h i (Finset.mem_union_left _ hi)),
    hG η ξ (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem IsCylinder.smul {f : C(S → Bool, ℝ)} (a : ℝ) (hf : IsCylinder f) :
    IsCylinder (a • f) := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨F, fun η ξ h => by simp only [ContinuousMap.smul_apply]; rw [hF η ξ h]⟩

theorem isCylinder_const (a : ℝ) : IsCylinder (ContinuousMap.const (S → Bool) a) :=
  ⟨∅, fun _ _ _ => rfl⟩

/-- The cylinder part of the exclusion graph as a submodule. -/
noncomputable def exclusionCylSubmodule
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdom : ∀ i j η, c i j η ≤ γ i j) :
    Submodule ℝ (C(S → Bool, ℝ) × C(S → Bool, ℝ)) where
  carrier := {fg | fg ∈ exclusionGraph c γ ∧ IsCylinder fg.1}
  add_mem' hp hq := ⟨exclusionGraph_add_mem c γ hc_nonneg hγ_nonneg hdom hp.1 hq.1,
    hp.2.add hq.2⟩
  zero_mem' := ⟨exclusionGraph_zero_mem c γ, ⟨∅, fun _ _ _ => rfl⟩⟩
  smul_mem' a _ hp := ⟨exclusionGraph_smul_mem c γ a hp.1, hp.2.smul a⟩

theorem exclusionGraph_pmp (hc_nonneg : ∀ i j η, 0 ≤ c i j η) :
    ∀ fg ∈ exclusionGraph c γ, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0 := by
  intro fg hfg x hmax _
  rw [hfg.2 x]
  exact tsum_nonpos fun ij => mul_nonpos_of_nonneg_of_nonpos (hc_nonneg _ _ _)
    (sub_nonpos.2 (hmax _))

/-- Cylinder functions lie in the weighted domain. -/
theorem summable_of_isCylinder (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i)
    (hrows : ∃ M : ℝ, ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (f : C(S → Bool, ℝ)) (hf : IsCylinder f) :
    Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2) := by
  classical
  obtain ⟨F, hF⟩ := hf
  obtain ⟨M, hM⟩ := hrows
  let v : S → S × S → ℝ := fun a ij => if ij.1 = a then γ a ij.2 else 0
  let w : S → S × S → ℝ := fun a ij => if ij.2 = a then γ ij.1 a else 0
  have hv : ∀ a, Summable (v a) := by
    intro a
    have hinj : Function.Injective (fun j : S => (a, j)) := fun x y h => (Prod.ext_iff.1 h).2
    refine (hinj.summable_iff (fun ij hij => ?_)).1 ?_
    · simp only [v]
      rw [if_neg]
      rintro rfl
      exact hij ⟨ij.2, rfl⟩
    · simpa [v, Function.comp_def] using (hM a).1
  have hw : ∀ a, Summable (w a) := by
    intro a
    have hinj : Function.Injective (fun i : S => (i, a)) := fun x y h => (Prod.ext_iff.1 h).1
    refine (hinj.summable_iff (fun ij hij => ?_)).1 ?_
    · simp only [w]
      rw [if_neg]
      rintro rfl
      exact hij ⟨ij.1, rfl⟩
    · have : (fun i => γ i a) = γ a := funext fun i => hγ_symm i a
      simpa [w, Function.comp_def, this] using (hM a).1
  have hsum : Summable (fun ij => (2 * ‖f‖) * ∑ a ∈ F, (v a ij + w a ij)) :=
    (summable_sum fun a _ => (hv a).add (hw a)).mul_left _
  refine Summable.of_nonneg_of_le (fun ij => mul_nonneg (hγ_nonneg _ _)
    (exclusionVariation_nonneg _ _ _)) (fun ij => ?_) hsum
  obtain ⟨i, j⟩ := ij
  have hvw : ∀ a, 0 ≤ v a (i, j) + w a (i, j) := fun a =>
    add_nonneg (by simp only [v]; split_ifs <;> simp [hγ_nonneg])
      (by simp only [w]; split_ifs <;> simp [hγ_nonneg])
  have hev := exclusionVariation_le_two_norm f i j
  have hγ := hγ_nonneg i j
  have h2 : 0 ≤ 2 * ‖f‖ := by positivity
  by_cases hi : i ∈ F
  · have : γ i j ≤ ∑ a ∈ F, (v a (i, j) + w a (i, j)) := by
      refine le_trans ?_ (Finset.single_le_sum (fun a _ => hvw a) hi)
      have : 0 ≤ w i (i, j) := by simp only [w]; split_ifs <;> simp [hγ_nonneg]
      simp only [v, if_true]; linarith
    nlinarith [exclusionVariation_nonneg f i j]
  by_cases hj : j ∈ F
  · have : γ i j ≤ ∑ a ∈ F, (v a (i, j) + w a (i, j)) := by
      refine le_trans ?_ (Finset.single_le_sum (fun a _ => hvw a) hj)
      have : 0 ≤ v j (i, j) := by simp only [v]; split_ifs <;> simp [hγ_nonneg]
      simp only [w, if_true]; linarith
    nlinarith [exclusionVariation_nonneg f i j]
  · have h0 : exclusionVariation f i j = 0 := by
      refine le_antisymm ((exclusionVariation_le_iff f i j 0).2 fun η => ?_)
        (exclusionVariation_nonneg f i j)
      rw [hF (exclusionExchange i j η) η (fun k hk => ?_), sub_self, abs_zero]
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      simp [exclusionExchange, hki, hkj]
    rw [h0, mul_zero]
    exact mul_nonneg h2 (Finset.sum_nonneg fun a _ => hvw a)

omit c γ in
/-- The subalgebra of cylinder functions. -/
noncomputable def cylSubalgebra : Subalgebra ℝ C(S → Bool, ℝ) where
  carrier := {f | IsCylinder f}
  mul_mem' := IsCylinder.mul
  add_mem' := IsCylinder.add
  algebraMap_mem' _ := ⟨∅, fun _ _ _ => rfl⟩

omit c γ in
/-- Cylinder functions are dense (Stone–Weierstrass). -/
theorem dense_isCylinder : Dense {f : C(S → Bool, ℝ) | IsCylinder f} := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (cylSubalgebra (S := S)) ?_
  · have : closure ((cylSubalgebra (S := S)) : Set C(S → Bool, ℝ)) = Set.univ := by
      rw [← Subalgebra.topologicalClosure_coe, h]; rfl
    exact dense_iff_closure_eq.2 this
  · intro η ξ hne
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    let g : C(S → Bool, ℝ) := ⟨fun ζ => if ζ i then 1 else 0,
      (continuous_of_discreteTopology (f := fun b : Bool => if b then (1:ℝ) else 0)).comp
        (continuous_apply i)⟩
    refine ⟨g, ⟨g, ⟨{i}, fun a b h => ?_⟩, rfl⟩, ?_⟩
    · simp [g, h i (Finset.mem_singleton_self i)]
    · simp only [g, ContinuousMap.coe_mk]
      cases hη : η i <;> cases hξ : ξ i <;> simp_all

end Exclusion

end EthierKurtz.ExclusionReduction

open EthierKurtz EthierKurtz.ExclusionReduction

/-- Ethier–Kurtz, Chapter 8, Theorem 3.6. -/
theorem solution (S : Type*) [Countable S]
    (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η)
    (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdiag : ∀ i, c i i = 0)
    (hc_symm : ∀ i j, c i j = c j i)
    (hdom : ∀ i j η, c i j η ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i)
    (hrows : ∃ M : ℝ, ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (hinfluence : ∃ K : ℝ, ∀ i j,
      Summable (spinVariation (c i j)) ∧
        (∑' k, spinVariation (c i j) k) ≤ K * γ i j) :
    let graph := exclusionGraph c γ
    let A := closure graph
    (∀ f : C(S → Bool, ℝ),
      Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation f ij.1 ij.2) →
      ∃ g, (f, g) ∈ graph) ∧
    (∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂) ∧
    (∃ T : ℝ → C(S → Bool, ℝ) →L[ℝ] C(S → Bool, ℝ),
      IsStronglyContinuousContractionSemigroup T ∧
      (∀ t : ℝ, 0 ≤ t → ∀ f, (∀ η, 0 ≤ f η) → ∀ η, 0 ≤ T t f η) ∧
      (∀ t : ℝ, 0 ≤ t → T t 1 = 1) ∧
      (∀ f g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f))
        (𝓝[>] (0 : ℝ)) (𝓝 g) ↔ (f, g) ∈ A)) ∧
    closure {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
      fg ∈ graph ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
        (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ} = A := by
  intro graph A
  set Gc := exclusionCylSubmodule c γ hc_nonneg hγ_nonneg hdom with hGc
  set Gf := exclusionSubmodule c γ hc_nonneg hγ_nonneg hdom with hGf
  have hGc_set : (Gc : Set _) = {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
      fg ∈ graph ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
        (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ} := rfl
  have hGf_set : (Gf : Set _) = graph := rfl
  obtain ⟨r, hr, hrange⟩ := exclusion_cylinder_range_dense S c γ hc_nonneg hγ_nonneg hdiag
    hc_symm hdom hγ_symm hrows hinfluence
  rw [← hGc_set] at hrange
  have hle : Gc ≤ Gf := fun p hp => hp.1
  have hdiss := dissipative_closure_of_pmp Gf
    (fun fg hfg => exclusionGraph_pmp c γ hc_nonneg fg hfg) r
  have hcl : closure (Gc : Set _) = A :=
    closure_eq_of_dissipative_of_denseRange Gc Gf hle r hr hdiss hrange
  have hpmp_c : ∀ fg ∈ Gc, ∀ x, (∀ y, fg.1 y ≤ fg.1 x) → 0 ≤ fg.1 x → fg.2 x ≤ 0 :=
    fun fg hfg => exclusionGraph_pmp c γ hc_nonneg fg hfg.1
  have hdense : Dense (Prod.fst '' (Gc : Set (C(S → Bool, ℝ) × C(S → Bool, ℝ)))) := by
    refine (dense_isCylinder (S := S)).mono ?_
    intro f hf
    obtain ⟨g, hg⟩ := exists_mem_exclusionGraph c γ hc_nonneg hdom f
      (summable_of_isCylinder γ hγ_nonneg hγ_symm hrows f hf)
    exact ⟨(f, g), ⟨hg, hf⟩, rfl⟩
  have hone : ((1 : C(S → Bool, ℝ)), (0 : C(S → Bool, ℝ))) ∈
      closure (Gc : Set (C(S → Bool, ℝ) × C(S → Bool, ℝ))) := by
    apply subset_closure
    obtain ⟨g, hg⟩ := exists_mem_exclusionGraph c γ hc_nonneg hdom (1 : C(S → Bool, ℝ))
      (summable_of_isCylinder γ hγ_nonneg hγ_symm hrows 1 ⟨∅, fun _ _ _ => rfl⟩)
    refine ⟨⟨hg.1, fun η => ?_⟩, ⟨∅, fun _ _ _ => rfl⟩⟩
    simp
  obtain ⟨T, hT, hpos, hcons, hgen⟩ := feller_generation_of_positive_maximum Gc hpmp_c hdense
    ⟨r, hr, hrange⟩ hone
  rw [hcl] at hgen
  refine ⟨fun f hf => exists_mem_exclusionGraph c γ hc_nonneg hdom f hf, ?_,
    ⟨T, hT, hpos, hcons, hgen⟩, ?_⟩
  · intro f g₁ g₂ h₁ h₂
    exact tendsto_nhds_unique ((hgen f g₁).2 h₁) ((hgen f g₂).2 h₂)
  · rw [← hGc_set]; exact hcl

