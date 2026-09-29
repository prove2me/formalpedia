-- Prove2me | solution 1 for EthierKurtz.exclusion_cylinder_range_dense
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T19:26:26.003652+00:00
-- url     : https://prove2.me/submissions/7d51994d-0f4d-4282-a35a-89ae5d72d4b8

import Definitions.Def_EthierKurtz_exclusionGraph
import Definitions.Def_EthierKurtz_spinVariation

open Filter
open scoped Topology BigOperators ENNReal

namespace EthierKurtz.ExclusionRangeProof

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


section Flip

variable {S : Type*}

theorem abs_sub_le_two_norm' (f : C(S → Bool, ℝ)) (a b : S → Bool) :
    |f a - f b| ≤ 2 * ‖f‖ := abs_sub_le_two_norm f a b

theorem bddAbove_range_flip (f : C(S → Bool, ℝ)) (i : S) :
    BddAbove (Set.range (fun η : S → Bool => |f (spinFlip i η) - f η|)) :=
  ⟨2 * ‖f‖, by rintro _ ⟨η, rfl⟩; exact abs_sub_le_two_norm f _ _⟩

theorem abs_sub_le_spinVariation (f : C(S → Bool, ℝ)) (i : S) (η : S → Bool) :
    |f (spinFlip i η) - f η| ≤ spinVariation f i :=
  le_csSup (bddAbove_range_flip f i) ⟨η, rfl⟩

theorem spinVariation_nonneg (f : C(S → Bool, ℝ)) (i : S) : 0 ≤ spinVariation f i :=
  (abs_nonneg _).trans (abs_sub_le_spinVariation f i (fun _ => false))

theorem spinVariation_le_iff (f : C(S → Bool, ℝ)) (i : S) (b : ℝ) :
    spinVariation f i ≤ b ↔ ∀ η, |f (spinFlip i η) - f η| ≤ b := by
  refine ⟨fun h η => (abs_sub_le_spinVariation f i η).trans h, fun h => ?_⟩
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨η, rfl⟩; exact h η)

theorem spinFlip_apply (i k : S) (η : S → Bool) [DecidableEq S] :
    spinFlip i η k = if k = i then !η i else η k := by
  unfold spinFlip
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem spinFlip_apply_of_ne {i k : S} (h : k ≠ i) (η : S → Bool) :
    spinFlip i η k = η k := by
  classical
  rw [spinFlip_apply, if_neg h]

theorem spinFlip_apply_self (i : S) (η : S → Bool) : spinFlip i η i = !η i := by
  classical
  rw [spinFlip_apply, if_pos rfl]

theorem spinFlip_spinFlip (i : S) (η : S → Bool) : spinFlip i (spinFlip i η) = η := by
  classical
  funext k; simp only [spinFlip_apply]; split_ifs <;> simp_all

theorem exclusionExchange_apply (i j k : S) (η : S → Bool) [DecidableEq S] :
    exclusionExchange i j η k = if k = i then η j else if k = j then η i else η k := by
  unfold exclusionExchange
  split_ifs <;> simp_all

theorem exchange_self (i : S) (η : S → Bool) : exclusionExchange i i η = η := by
  classical
  funext k; rw [exclusionExchange_apply]; split_ifs; all_goals simp_all

theorem exchange_of_eq {i j : S} {η : S → Bool} (h : η i = η j) :
    exclusionExchange i j η = η := by
  classical
  funext k; rw [exclusionExchange_apply]; split_ifs; all_goals simp_all

theorem exchange_of_ne {i j : S} {η : S → Bool} (h : η i ≠ η j) :
    exclusionExchange i j η = spinFlip i (spinFlip j η) := by
  classical
  have hij : i ≠ j := fun e => h (e ▸ rfl)
  have hj : η j = !η i := by cases hi : η i <;> cases hj : η j <;> simp_all
  funext k; simp only [exclusionExchange_apply, spinFlip_apply]
  by_cases hki : k = i
  · subst hki; simp [hij, hj]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, hj]
    · simp [hki, hkj]

theorem exchange_flip_of_ne {i j k : S} (hi : k ≠ i) (hj : k ≠ j) (η : S → Bool) :
    exclusionExchange i j (spinFlip k η) = spinFlip k (exclusionExchange i j η) := by
  classical
  funext m; simp only [exclusionExchange_apply, spinFlip_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem exchange_flip_left {i j : S} (hij : i ≠ j) (η : S → Bool) :
    exclusionExchange i j (spinFlip i η) = spinFlip j (exclusionExchange i j η) := by
  classical
  funext m; simp only [exclusionExchange_apply, spinFlip_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem exchange_flip_right {i j : S} (hij : i ≠ j) (η : S → Bool) :
    exclusionExchange i j (spinFlip j η) = spinFlip i (exclusionExchange i j η) := by
  classical
  funext m; simp only [exclusionExchange_apply, spinFlip_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem abs_exchange_le_spinVariation (f : C(S → Bool, ℝ)) (i j : S) (η : S → Bool) :
    |f (exclusionExchange i j η) - f η| ≤ spinVariation f i + spinVariation f j := by
  by_cases h : η i = η j
  · rw [exchange_of_eq h, sub_self, abs_zero]
    exact add_nonneg (spinVariation_nonneg f i) (spinVariation_nonneg f j)
  · rw [exchange_of_ne h]
    calc |f (spinFlip i (spinFlip j η)) - f η|
        = |(f (spinFlip i (spinFlip j η)) - f (spinFlip j η)) + (f (spinFlip j η) - f η)| := by
          ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_sub_le_spinVariation f i _) (abs_sub_le_spinVariation f j η)

end Flip

section Freeze

variable {S : Type*}

/-- Keep the coordinates in `F` and replace the others by those of `ξ`. -/
noncomputable def freeze (F : Finset S) (ξ η : S → Bool) : S → Bool := by
  classical
  exact fun k => if k ∈ F then η k else ξ k

theorem freeze_apply_of_mem {F : Finset S} {k : S} (hk : k ∈ F) (ξ η : S → Bool) :
    freeze F ξ η k = η k := by
  classical
  unfold freeze; split_ifs; all_goals simp_all

theorem freeze_apply_of_not_mem {F : Finset S} {k : S} (hk : k ∉ F) (ξ η : S → Bool) :
    freeze F ξ η k = ξ k := by
  classical
  unfold freeze; split_ifs; all_goals simp_all

theorem freeze_congr {F : Finset S} (ξ : S → Bool) {η ζ : S → Bool}
    (h : ∀ i ∈ F, η i = ζ i) : freeze F ξ η = freeze F ξ ζ := by
  funext k
  by_cases hk : k ∈ F
  · rw [freeze_apply_of_mem hk, freeze_apply_of_mem hk, h k hk]
  · rw [freeze_apply_of_not_mem hk, freeze_apply_of_not_mem hk]

theorem continuous_freeze (F : Finset S) (ξ : S → Bool) : Continuous (freeze F ξ) := by
  classical
  refine continuous_pi fun k => ?_
  by_cases hk : k ∈ F
  · simp only [freeze_apply_of_mem hk]; exact continuous_apply k
  · simp only [freeze_apply_of_not_mem hk]; exact continuous_const

theorem freeze_spinFlip_of_mem {F : Finset S} {k : S} (hk : k ∈ F) (ξ η : S → Bool) :
    freeze F ξ (spinFlip k η) = spinFlip k (freeze F ξ η) := by
  classical
  funext m
  by_cases hm : m ∈ F
  · rw [freeze_apply_of_mem hm, spinFlip_apply, spinFlip_apply, freeze_apply_of_mem hm,
      freeze_apply_of_mem hk]
  · have hmk : m ≠ k := fun e => hm (e ▸ hk)
    rw [freeze_apply_of_not_mem hm, spinFlip_apply_of_ne hmk, freeze_apply_of_not_mem hm]

theorem freeze_spinFlip_of_not_mem {F : Finset S} {k : S} (hk : k ∉ F) (ξ η : S → Bool) :
    freeze F ξ (spinFlip k η) = freeze F ξ η := by
  refine freeze_congr ξ fun i hi => ?_
  exact spinFlip_apply_of_ne (by rintro rfl; exact hk hi) η

/-- A continuous function depends only on `F` iff it is invariant under freezing. -/
theorem apply_freeze_of_dependsOn {F : Finset S} {f : C(S → Bool, ℝ)}
    (hf : ∀ η ζ : S → Bool, (∀ i ∈ F, η i = ζ i) → f η = f ζ) (ξ η : S → Bool) :
    f (freeze F ξ η) = f η :=
  hf _ _ fun _ hi => freeze_apply_of_mem hi ξ η

theorem exchange_agree_on {F : Finset S} {i j : S} (hi : i ∈ F) (hj : j ∈ F)
    {η ζ : S → Bool} (h : ∀ k ∈ F, η k = ζ k) :
    ∀ k ∈ F, exclusionExchange i j η k = exclusionExchange i j ζ k := by
  classical
  intro k hk
  simp only [exclusionExchange_apply]
  split_ifs
  · exact h j hj
  · exact h i hi
  · exact h k hk

end Freeze

section FiniteSolve

variable {S : Type*}

/-- Solvability of the finite frozen-rate resolvent equation. -/
theorem exists_frozen_solution (F : Finset S) (ξ : S → Bool)
    (b : S → S → C(S → Bool, ℝ)) (hb : ∀ i j η, 0 ≤ b i j η) (r : ℝ) (hr : 0 < r)
    (h : C(S → Bool, ℝ)) (hh : ∀ η ζ : S → Bool, (∀ i ∈ F, η i = ζ i) → h η = h ζ) :
    ∃ u : C(S → Bool, ℝ), (∀ η ζ : S → Bool, (∀ i ∈ F, η i = ζ i) → u η = u ζ) ∧
      ∀ η, r * u η - ∑ i ∈ F, ∑ j ∈ F,
        b i j (freeze F ξ η) * (u (exclusionExchange i j η) - u η) = h η := by
  classical
  let embed : (F → Bool) → S → Bool := fun y k => if hk : k ∈ F then y ⟨k, hk⟩ else ξ k
  let restr : (S → Bool) → F → Bool := fun η k => η k
  have hER : ∀ η, embed (restr η) = freeze F ξ η := by
    intro η; funext k
    by_cases hk : k ∈ F
    · simp [embed, restr, hk, freeze_apply_of_mem hk]
    · simp [embed, hk, freeze_apply_of_not_mem hk]
  let sw : S → S → (F → Bool) → (F → Bool) := fun i j y =>
    restr (exclusionExchange i j (embed y))
  let Lf : ((F → Bool) → ℝ) → (F → Bool) → ℝ := fun U y =>
    r * U y - ∑ i ∈ F, ∑ j ∈ F, b i j (embed y) * (U (sw i j y) - U y)
  let L : ((F → Bool) → ℝ) →ₗ[ℝ] ((F → Bool) → ℝ) :=
    { toFun := Lf
      map_add' := by
        intro U V; funext y
        simp only [Lf, Pi.add_apply]
        rw [show (∑ i ∈ F, ∑ j ∈ F, b i j (embed y) *
              (U (sw i j y) + V (sw i j y) - (U y + V y)))
          = (∑ i ∈ F, ∑ j ∈ F, b i j (embed y) * (U (sw i j y) - U y)) +
            ∑ i ∈ F, ∑ j ∈ F, b i j (embed y) * (V (sw i j y) - V y) by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
          ring]
        ring
      map_smul' := by
        intro a U; funext y
        simp only [Lf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [show (∑ i ∈ F, ∑ j ∈ F, b i j (embed y) * (a * U (sw i j y) - a * U y))
          = a * ∑ i ∈ F, ∑ j ∈ F, b i j (embed y) * (U (sw i j y) - U y) by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
          ring]
        ring }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro U hU
    have hU' : ∀ y, Lf U y = 0 := fun y => congrFun hU y
    obtain ⟨y1, hy1⟩ := Finite.exists_max U
    obtain ⟨y2, hy2⟩ := Finite.exists_min U
    have h1 : U y1 ≤ 0 := by
      have e := hU' y1
      have : ∑ i ∈ F, ∑ j ∈ F, b i j (embed y1) * (U (sw i j y1) - U y1) ≤ 0 :=
        Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ =>
          mul_nonpos_of_nonneg_of_nonpos (hb _ _ _) (sub_nonpos.2 (hy1 _))
      simp only [Lf] at e
      nlinarith
    have h2 : 0 ≤ U y2 := by
      have e := hU' y2
      have : 0 ≤ ∑ i ∈ F, ∑ j ∈ F, b i j (embed y2) * (U (sw i j y2) - U y2) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hb _ _ _) (sub_nonneg.2 (hy2 _))
      simp only [Lf] at e
      nlinarith
    funext y
    exact le_antisymm ((hy1 y).trans h1) (h2.trans (hy2 y))
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  obtain ⟨U, hU⟩ := hsurj (fun y => h (embed y))
  have hrestr : Continuous restr := continuous_pi fun k => continuous_apply (k : S)
  refine ⟨⟨fun η => U (restr η), continuous_of_discreteTopology.comp hrestr⟩, ?_, ?_⟩
  · intro η ζ hηζ
    show U (restr η) = U (restr ζ)
    congr 1; funext k; exact hηζ k k.2
  · intro η
    have e := congrFun hU (restr η)
    change Lf U (restr η) = h (embed (restr η)) at e
    simp only [Lf, hER] at e
    rw [apply_freeze_of_dependsOn hh] at e
    rw [← e]
    simp only [ContinuousMap.coe_mk]
    congr 1
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    congr 2
    simp only [sw, hER]
    congr 1
    funext k
    exact (exchange_agree_on hi hj (fun m hm => (freeze_apply_of_mem hm ξ η)) k k.2).symm

end FiniteSolve

section Estimate

variable {S : Type*}

/-- Liggett's variation estimate for the finite frozen-rate resolvent equation. -/
theorem frozen_variation_estimate (F : Finset S) (ξ : S → Bool)
    (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η) (hdom : ∀ i j η, c i j η ≤ γ i j)
    (r : ℝ) (hr : 0 ≤ r) (h u : C(S → Bool, ℝ))
    (hu : ∀ η, r * u η - ∑ i ∈ F, ∑ j ∈ F,
        c i j (freeze F ξ η) * (u (exclusionExchange i j η) - u η) = h η)
    (k : S) (hk : k ∈ F) :
    r * spinVariation u k ≤ spinVariation h k + ∑ j ∈ F, γ k j * spinVariation u j +
      ∑ i ∈ F, γ i k * spinVariation u i +
      ∑ i ∈ F, ∑ j ∈ F, spinVariation (c i j) k * (spinVariation u i + spinVariation u j) := by
  classical
  set v : S → ℝ := fun m => spinVariation u m with hv
  let D : (S → Bool) → ℝ := fun η => u (spinFlip k η) - u η
  have hDc : Continuous D := by
    have : Continuous (spinFlip k : (S → Bool) → S → Bool) := by
      refine continuous_pi fun m => ?_
      by_cases hm : m = k
      · subst hm
        simp only [spinFlip_apply_self]
        exact (continuous_of_discreteTopology (f := fun b : Bool => !b)).comp (continuous_apply m)
      · simp only [spinFlip_apply_of_ne hm]; exact continuous_apply m
    exact (u.continuous.comp this).sub u.continuous
  obtain ⟨η, -, hη⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hDc.continuousOn
  have hmax : ∀ ζ, D ζ ≤ D η := fun ζ => hη (Set.mem_univ ζ)
  have hvk : v k ≤ D η := by
    refine (spinVariation_le_iff u k _).2 fun ζ => abs_le.2 ⟨?_, hmax ζ⟩
    have := hmax (spinFlip k ζ)
    simp only [D, spinFlip_spinFlip] at this
    linarith
  have hv0 : ∀ m, 0 ≤ v m := fun m => spinVariation_nonneg u m
  -- the rates at the two configurations
  set η' := spinFlip k η with hη'
  have hfr : freeze F ξ η' = spinFlip k (freeze F ξ η) := freeze_spinFlip_of_mem hk ξ η
  have hterm : ∀ i ∈ F, ∀ j ∈ F,
      c i j (freeze F ξ η') * (u (exclusionExchange i j η') - u η') -
        c i j (freeze F ξ η) * (u (exclusionExchange i j η) - u η) ≤
      ((if k = i then γ k j * v j else 0) + (if k = j then γ i k * v i else 0)) +
        spinVariation (c i j) k * (v i + v j) := by
    intro i _ j _
    set b' := c i j (freeze F ξ η')
    set b := c i j (freeze F ξ η)
    have hb : 0 ≤ b := hc_nonneg _ _ _
    have hbγ : b ≤ γ i j := hdom _ _ _
    have hdiff : |b' - b| ≤ spinVariation (c i j) k := by
      simp only [b', b, hfr]; exact abs_sub_le_spinVariation _ _ _
    have hex : |u (exclusionExchange i j η') - u η'| ≤ v i + v j :=
      abs_exchange_le_spinVariation u i j η'
    have hsplit : b' * (u (exclusionExchange i j η') - u η') - b * (u (exclusionExchange i j η) - u η)
        = b * (u (exclusionExchange i j η') - u (exclusionExchange i j η) - D η) +
          (b' - b) * (u (exclusionExchange i j η') - u η') := by
      simp only [D, hη']; ring
    have hsecond : (b' - b) * (u (exclusionExchange i j η') - u η') ≤
        spinVariation (c i j) k * (v i + v j) := by
      calc (b' - b) * (u (exclusionExchange i j η') - u η')
          ≤ |(b' - b) * (u (exclusionExchange i j η') - u η')| := le_abs_self _
        _ = |b' - b| * |u (exclusionExchange i j η') - u η'| := abs_mul _ _
        _ ≤ _ := mul_le_mul hdiff hex (abs_nonneg _) (spinVariation_nonneg _ _)
    have hfirst : b * (u (exclusionExchange i j η') - u (exclusionExchange i j η) - D η) ≤
        (if k = i then γ k j * v j else 0) + (if k = j then γ i k * v i else 0) := by
      by_cases hki : k = i
      · by_cases hkj : k = j
        · -- i = j = k
          subst hki; subst hkj
          simp only [exchange_self, D, hη', if_true]
          have : b * (u (spinFlip k η) - u η - (u (spinFlip k η) - u η)) = 0 := by ring
          rw [this]
          exact add_nonneg (mul_nonneg ((hc_nonneg k k η).trans (hdom k k η)) (hv0 k))
            (mul_nonneg ((hc_nonneg k k η).trans (hdom k k η)) (hv0 k))
        · subst hki
          have hij : k ≠ j := hkj
          rw [if_pos rfl, if_neg hkj, add_zero, hη', exchange_flip_left hij]
          have hx : u (spinFlip j (exclusionExchange k j η)) - u (exclusionExchange k j η) - D η
              ≤ v j := by
            have h1 := abs_sub_le_spinVariation u j (exclusionExchange k j η)
            have h2 := (hv0 k).trans hvk
            linarith [le_abs_self (u (spinFlip j (exclusionExchange k j η)) -
              u (exclusionExchange k j η))]
          calc _ ≤ b * v j := mul_le_mul_of_nonneg_left hx hb
            _ ≤ γ k j * v j := mul_le_mul_of_nonneg_right hbγ (hv0 j)
      · by_cases hkj : k = j
        · subst hkj
          have hij : i ≠ k := fun e => hki e.symm
          rw [if_neg hki, if_pos rfl, zero_add, hη', exchange_flip_right hij]
          have hx : u (spinFlip i (exclusionExchange i k η)) - u (exclusionExchange i k η) - D η
              ≤ v i := by
            have h1 := abs_sub_le_spinVariation u i (exclusionExchange i k η)
            have h2 := (hv0 k).trans hvk
            linarith [le_abs_self (u (spinFlip i (exclusionExchange i k η)) -
              u (exclusionExchange i k η))]
          calc _ ≤ b * v i := mul_le_mul_of_nonneg_left hx hb
            _ ≤ γ i k * v i := mul_le_mul_of_nonneg_right hbγ (hv0 i)
        · rw [if_neg hki, if_neg hkj, add_zero, hη',
            exchange_flip_of_ne (fun e => hki e) (fun e => hkj e)]
          have : u (spinFlip k (exclusionExchange i j η)) - u (exclusionExchange i j η) - D η ≤ 0 := by
            have := hmax (exclusionExchange i j η); simp only [D] at this; linarith
          exact mul_nonpos_of_nonneg_of_nonpos hb this
    rw [hsplit]
    linarith
  -- sum up
  have hsum := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  have heq : r * D η = (h η' - h η) +
      ∑ i ∈ F, ∑ j ∈ F, (c i j (freeze F ξ η') * (u (exclusionExchange i j η') - u η') -
        c i j (freeze F ξ η) * (u (exclusionExchange i j η) - u η)) := by
    have e1 := hu η'
    have e2 := hu η
    simp only [Finset.sum_sub_distrib]
    simp only [D, hη'] at *
    linarith
  have hh : h η' - h η ≤ spinVariation h k :=
    (le_abs_self _).trans (abs_sub_le_spinVariation h k η)
  have hind : ∑ i ∈ F, ∑ j ∈ F,
      (((if k = i then γ k j * v j else 0) + (if k = j then γ i k * v i else 0)) +
        spinVariation (c i j) k * (v i + v j)) =
      ∑ j ∈ F, γ k j * v j + ∑ i ∈ F, γ i k * v i +
        ∑ i ∈ F, ∑ j ∈ F, spinVariation (c i j) k * (v i + v j) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm (f := fun i j => if k = j then γ i k * v i else 0)]
    simp [Finset.sum_ite_eq, hk]
  calc r * v k ≤ r * D η := mul_le_mul_of_nonneg_left hvk hr
    _ ≤ _ := by rw [heq]; linarith

end Estimate

section Domination

variable {S : Type*}

/-- Iterates `Γ^m a` of a nonnegative infinite matrix acting on a nonnegative vector. -/
noncomputable def matIter (Γ : S → S → ℝ≥0∞) (a : S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0 => a
  | m + 1 => fun k => ∑' l, Γ k l * matIter Γ a m l

theorem tsum_matIter_succ_le (Γ : S → S → ℝ≥0∞) (C : ℝ≥0∞) (hcol : ∀ l, ∑' k, Γ k l ≤ C)
    (x : S → ℝ≥0∞) (m : ℕ) :
    ∑' k, matIter Γ x (m + 1) k ≤ C * ∑' k, matIter Γ x m k := by
  simp only [matIter]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun l => ?_
  rw [ENNReal.tsum_mul_right]
  gcongr
  exact hcol l

theorem tsum_matIter_le (Γ : S → S → ℝ≥0∞) (C : ℝ≥0∞) (hcol : ∀ l, ∑' k, Γ k l ≤ C)
    (x : S → ℝ≥0∞) (m : ℕ) :
    ∑' k, matIter Γ x m k ≤ C ^ m * ∑' k, x k := by
  induction m with
  | zero => simp [matIter]
  | succ m ih =>
    calc ∑' k, matIter Γ x (m + 1) k ≤ C * ∑' k, matIter Γ x m k :=
          tsum_matIter_succ_le Γ C hcol x m
      _ ≤ C * (C ^ m * ∑' k, x k) := by gcongr
      _ = C ^ (m + 1) * ∑' k, x k := by rw [pow_succ]; ring

theorem le_partial_add_tail (Γ : S → S → ℝ≥0∞) (ρ : ℝ≥0∞) (a v : S → ℝ≥0∞)
    (hv : ∀ k, v k ≤ ρ * (a k + ∑' l, Γ k l * v l)) (N : ℕ) :
    ∀ k, v k ≤ (∑ m ∈ Finset.range N, ρ ^ (m + 1) * matIter Γ a m k) +
      ρ ^ N * matIter Γ v N k := by
  induction N with
  | zero => intro k; simp [matIter]
  | succ N ih =>
    intro k
    calc v k ≤ ρ * (a k + ∑' l, Γ k l * v l) := hv k
      _ ≤ ρ * (a k + ∑' l, Γ k l * ((∑ m ∈ Finset.range N, ρ ^ (m + 1) * matIter Γ a m l) +
            ρ ^ N * matIter Γ v N l)) := by
          gcongr with l; exact ih l
      _ = (∑ m ∈ Finset.range (N + 1), ρ ^ (m + 1) * matIter Γ a m k) +
            ρ ^ (N + 1) * matIter Γ v (N + 1) k := by
          simp only [mul_add, ENNReal.tsum_add, Finset.mul_sum]
          rw [Finset.sum_range_succ', Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          have e1 : ∀ i, ∑' l, Γ k l * (ρ ^ (i + 1) * matIter Γ a i l) =
              ρ ^ (i + 1) * matIter Γ a (i + 1) k := by
            intro i
            simp only [matIter]
            rw [← ENNReal.tsum_mul_left]
            congr 1; funext l; ring
          have e2 : ∑' l, Γ k l * (ρ ^ N * matIter Γ v N l) =
              ρ ^ N * matIter Γ v (N + 1) k := by
            simp only [matIter]
            rw [← ENNReal.tsum_mul_left]
            congr 1; funext l; ring
          rw [e2, Finset.mul_sum]
          simp only [e1]
          have h0 : matIter Γ a 0 k = a k := rfl
          rw [h0]
          have : ∀ i ∈ Finset.range N, ρ * (ρ ^ (i + 1) * matIter Γ a (i + 1) k) =
              ρ ^ (i + 1 + 1) * matIter Γ a (i + 1) k := by
            intro i _; ring
          rw [Finset.sum_congr rfl this]
          ring

/-- Uniform domination of finitely supported subsolutions of `r v ≤ a + Γ v` by a fixed
summable sequence, when the column sums of `Γ` are at most `C < r`. -/
theorem exists_dominating_sequence (Γ : S → S → ℝ) (hΓ : ∀ k l, 0 ≤ Γ k l) (C r : ℝ)
    (hC : 0 ≤ C) (hr : C < r)
    (hcol : ∀ l, Summable (fun k => Γ k l) ∧ ∑' k, Γ k l ≤ C)
    (a : S → ℝ) (ha : ∀ k, 0 ≤ a k) (has : Summable a) :
    ∃ w : S → ℝ, (∀ k, 0 ≤ w k) ∧ Summable w ∧
      ∀ (v : S → ℝ) (F : Finset S), (∀ k, 0 ≤ v k) → (∀ k ∉ F, v k = 0) →
        (∀ k ∈ F, r * v k ≤ a k + ∑ l ∈ F, Γ k l * v l) → ∀ k, v k ≤ w k := by
  classical
  have hr0 : 0 < r := hC.trans_lt hr
  set Γ' : S → S → ℝ≥0∞ := fun k l => ENNReal.ofReal (Γ k l)
  set a' : S → ℝ≥0∞ := fun k => ENNReal.ofReal (a k)
  set ρ : ℝ≥0∞ := ENNReal.ofReal r⁻¹
  set C' : ℝ≥0∞ := ENNReal.ofReal C
  have hcol' : ∀ l, ∑' k, Γ' k l ≤ C' := by
    intro l
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => hΓ k l) (hcol l).1]
    exact ENNReal.ofReal_le_ofReal (hcol l).2
  have hq : C' * ρ < 1 := by
    rw [← ENNReal.ofReal_mul hC, ENNReal.ofReal_lt_one]
    rw [← div_eq_mul_inv, div_lt_one hr0]; exact hr
  have hA : ∑' k, a' k ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg ha has]; exact ENNReal.ofReal_ne_top
  set w' : S → ℝ≥0∞ := fun k => ∑' m, ρ ^ (m + 1) * matIter Γ' a' m k
  have hW : ∑' k, w' k ≠ ∞ := by
    have : ∑' k, w' k ≤ ρ * (∑' k, a' k) * (1 - C' * ρ)⁻¹ := by
      simp only [w']
      rw [ENNReal.tsum_comm]
      calc ∑' m, ∑' k, ρ ^ (m + 1) * matIter Γ' a' m k
          = ∑' m, ρ ^ (m + 1) * ∑' k, matIter Γ' a' m k := by
            congr 1; funext m; rw [ENNReal.tsum_mul_left]
        _ ≤ ∑' m, ρ ^ (m + 1) * (C' ^ m * ∑' k, a' k) := by
            gcongr with m; exact tsum_matIter_le Γ' C' hcol' a' m
        _ = ∑' m, ρ * (∑' k, a' k) * (C' * ρ) ^ m := by
            congr 1; funext m; rw [mul_pow, pow_succ]; ring
        _ = ρ * (∑' k, a' k) * (1 - C' * ρ)⁻¹ := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ne_top_of_le_ne_top ?_ this
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) ?_
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hq).ne'
  have hw'fin : ∀ k, w' k ≠ ∞ := fun k => ne_top_of_le_ne_top hW (ENNReal.le_tsum k)
  refine ⟨fun k => (w' k).toReal, fun k => ENNReal.toReal_nonneg,
    ENNReal.summable_toReal hW, ?_⟩
  intro v F hv0 hvF hvest k
  set v' : S → ℝ≥0∞ := fun k => ENNReal.ofReal (v k)
  have hV : ∑' k, v' k ≠ ∞ := by
    rw [tsum_eq_sum (s := F) (fun k hk => by simp [v', hvF k hk])]
    exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  have hv' : ∀ k, v' k ≤ ρ * (a' k + ∑' l, Γ' k l * v' l) := by
    intro k
    by_cases hk : k ∈ F
    · have h1 : v k ≤ r⁻¹ * (a k + ∑ l ∈ F, Γ k l * v l) := by
        rw [← div_eq_inv_mul, le_div_iff₀ hr0, mul_comm]; exact hvest k hk
      calc v' k ≤ ENNReal.ofReal (r⁻¹ * (a k + ∑ l ∈ F, Γ k l * v l)) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ρ * (a' k + ∑ l ∈ F, Γ' k l * v' l) := by
            rw [ENNReal.ofReal_mul (inv_nonneg.2 hr0.le),
              ENNReal.ofReal_add (ha k)
                (Finset.sum_nonneg fun l _ => mul_nonneg (hΓ k l) (hv0 l)),
              ENNReal.ofReal_sum_of_nonneg (fun l _ => mul_nonneg (hΓ k l) (hv0 l))]
            simp only [ENNReal.ofReal_mul (hΓ _ _), Γ', v', a', ρ]
        _ ≤ ρ * (a' k + ∑' l, Γ' k l * v' l) := by
            gcongr; exact ENNReal.sum_le_tsum F
    · simp [v', hvF k hk]
  have hbound : ∀ N : ℕ, v' k ≤ w' k + (C' * ρ) ^ N * ∑' k, v' k := by
    intro N
    refine (le_partial_add_tail Γ' ρ a' v' hv' N k).trans (add_le_add ?_ ?_)
    · exact ENNReal.sum_le_tsum _
    · calc ρ ^ N * matIter Γ' v' N k ≤ ρ ^ N * (C' ^ N * ∑' k, v' k) := by
            gcongr
            exact (ENNReal.le_tsum k).trans (tsum_matIter_le Γ' C' hcol' v' N)
        _ = (C' * ρ) ^ N * ∑' k, v' k := by rw [mul_pow]; ring
  have htend : Tendsto (fun N : ℕ => w' k + (C' * ρ) ^ N * ∑' k, v' k) atTop (𝓝 (w' k)) := by
    have := (ENNReal.Tendsto.mul_const (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Or.inr hV))
    simpa using (tendsto_const_nhds (x := w' k)).add this
  have hle : v' k ≤ w' k := ge_of_tendsto' htend hbound
  calc v k = (v' k).toReal := (ENNReal.toReal_ofReal (hv0 k)).symm
    _ ≤ (w' k).toReal := ENNReal.toReal_mono (hw'fin k) hle

end Domination

section Assembly

variable {S : Type*}

/-- Uniform approximation: a continuous function almost depends on finitely many
coordinates. -/
theorem exists_finset_abs_sub_lt (g : C(S → Bool, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F0 : Finset S, ∀ η ζ : S → Bool, (∀ i ∈ F0, η i = ζ i) → |g η - g ζ| < ε := by
  obtain ⟨h, hh, hgh⟩ := Metric.dense_iff.1 (dense_isCylinder (S := S)) g (ε / 2) (by linarith)
  obtain ⟨F0, hF0⟩ := hgh
  refine ⟨F0, fun η ζ hηζ => ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hh
  have h1 : |g η - h η| < ε / 2 := by
    have := (g - h).norm_coe_le_norm η
    rw [Real.norm_eq_abs] at this
    simp only [ContinuousMap.sub_apply] at this
    linarith [norm_sub_rev g h]
  have h2 : |g ζ - h ζ| < ε / 2 := by
    have := (g - h).norm_coe_le_norm ζ
    rw [Real.norm_eq_abs] at this
    simp only [ContinuousMap.sub_apply] at this
    linarith [norm_sub_rev g h]
  rw [show g η - g ζ = (g η - h η) - (g ζ - h ζ) by rw [hF0 η ζ hηζ]; ring]
  calc |(g η - h η) - (g ζ - h ζ)| ≤ |g η - h η| + |g ζ - h ζ| := abs_sub _ _
    _ < ε := by linarith

theorem spinVariation_eq_zero_of_not_mem {F : Finset S} {f : C(S → Bool, ℝ)}
    (hf : ∀ η ζ : S → Bool, (∀ i ∈ F, η i = ζ i) → f η = f ζ) {k : S} (hk : k ∉ F) :
    spinVariation f k = 0 := by
  refine le_antisymm ((spinVariation_le_iff f k 0).2 fun η => ?_) (spinVariation_nonneg f k)
  rw [hf (spinFlip k η) η (fun i hi => spinFlip_apply_of_ne (by rintro rfl; exact hk hi) η),
    sub_self, abs_zero]

/-- The defect created by freezing the coordinates outside `F`. -/
noncomputable def freezeDefect (F : Finset S) (ξ : S → Bool) (g : C(S → Bool, ℝ)) : ℝ :=
  sSup (Set.range fun η : S → Bool => |g (freeze F ξ η) - g η|)

theorem abs_sub_le_freezeDefect (F : Finset S) (ξ : S → Bool) (g : C(S → Bool, ℝ))
    (η : S → Bool) : |g (freeze F ξ η) - g η| ≤ freezeDefect F ξ g :=
  le_csSup ⟨2 * ‖g‖, by rintro _ ⟨η, rfl⟩; exact abs_sub_le_two_norm g _ _⟩ ⟨η, rfl⟩

theorem freezeDefect_nonneg (F : Finset S) (ξ : S → Bool) (g : C(S → Bool, ℝ)) :
    0 ≤ freezeDefect F ξ g :=
  (abs_nonneg _).trans (abs_sub_le_freezeDefect F ξ g ξ)

theorem freezeDefect_le (F : Finset S) (ξ : S → Bool) (g : C(S → Bool, ℝ)) (b : ℝ)
    (hg0 : ∀ η, 0 ≤ g η) (hgb : ∀ η, g η ≤ b) : freezeDefect F ξ g ≤ b := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨η, rfl⟩
  have h1 := hg0 η; have h2 := hgb η; have h3 := hg0 (freeze F ξ η)
  have h4 := hgb (freeze F ξ η)
  rw [abs_le]; constructor <;> linarith

theorem tendsto_freezeDefect (ξ : S → Bool) (g : C(S → Bool, ℝ)) :
    Tendsto (fun F : Finset S => freezeDefect F ξ g) atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨F0, hF0⟩ := exists_finset_abs_sub_lt g (half_pos hε)
  filter_upwards [eventually_ge_atTop F0] with F hF
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (freezeDefect_nonneg F ξ g)]
  refine lt_of_le_of_lt (csSup_le (Set.range_nonempty _) ?_) (half_lt_self hε)
  rintro _ ⟨η, rfl⟩
  exact (hF0 _ _ fun i hi => freeze_apply_of_mem (hF hi) ξ η).le

/-- Summability of `γ(i,j) (w_i + w_j)` over ordered pairs. -/
theorem summable_gamma_mul_add (γ : S → S → ℝ) (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i) (M : ℝ) (hM : ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (w : S → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw : Summable w) :
    Summable (fun ij : S × S => γ ij.1 ij.2 * (w ij.1 + w ij.2)) := by
  have h1 : Summable (fun ij : S × S => γ ij.1 ij.2 * w ij.1) := by
    have hnn : 0 ≤ (fun ij : S × S => γ ij.1 ij.2 * w ij.1) := fun ij =>
      mul_nonneg (hγ_nonneg _ _) (hw0 _)
    refine (summable_prod_of_nonneg hnn).2 ⟨fun i => ?_, ?_⟩
    · exact (hM i).1.mul_right (w i)
    · refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j =>
        mul_nonneg (hγ_nonneg _ _) (hw0 _)) (fun i => ?_) (hw.mul_left M)
      show ∑' j, γ i j * w i ≤ M * w i
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (hM i).2 (hw0 i)
  have h2 : Summable (fun ij : S × S => γ ij.1 ij.2 * w ij.2) := by
    have := (Equiv.prodComm S S).summable_iff.2 h1
    refine this.congr fun ij => ?_
    show γ ij.2 ij.1 * w ij.2 = γ ij.1 ij.2 * w ij.2
    rw [hγ_symm ij.2 ij.1]
  exact (h1.add h2).congr fun ij => by ring

/-- The influence matrix of Liggett's estimate. -/
noncomputable def influenceMatrix (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ) (k l : S) : ℝ :=
  γ k l + γ l k + ∑' j, (spinVariation (c l j) k + spinVariation (c j l) k)

section InfluenceMatrix

variable (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
  (hγ_nonneg : ∀ i j, 0 ≤ γ i j) (hγ_symm : ∀ i j, γ i j = γ j i)
  (M K : ℝ) (hM : ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
  (hK : ∀ i j, Summable (spinVariation (c i j)) ∧ (∑' k, spinVariation (c i j) k) ≤ K * γ i j)

include hK in
theorem spinVariation_le_influence (i j k : S) : spinVariation (c i j) k ≤ K * γ i j :=
  ((hK i j).1.le_tsum k fun m _ => spinVariation_nonneg _ _).trans (hK i j).2

include hγ_nonneg hγ_symm hM hK in
theorem summable_influence_row (l k : S) :
    Summable (fun j => spinVariation (c l j) k + spinVariation (c j l) k) := by
  refine Summable.of_nonneg_of_le (fun j => add_nonneg (spinVariation_nonneg _ _)
    (spinVariation_nonneg _ _)) (fun j => ?_) ((hM l).1.mul_left (2 * K))
  have h1 := spinVariation_le_influence c γ K hK l j k
  have h2 := spinVariation_le_influence c γ K hK j l k
  rw [hγ_symm j l] at h2
  linarith

include hγ_nonneg hγ_symm hM hK in
theorem influenceMatrix_nonneg (k l : S) : 0 ≤ influenceMatrix c γ k l :=
  add_nonneg (add_nonneg (hγ_nonneg _ _) (hγ_nonneg _ _))
    (tsum_nonneg fun j => add_nonneg (spinVariation_nonneg _ _) (spinVariation_nonneg _ _))

include hγ_nonneg hγ_symm hM hK in
theorem influenceMatrix_col (hKnn : 0 ≤ K) (l : S) :
    Summable (fun k => influenceMatrix c γ k l) ∧
      ∑' k, influenceMatrix c γ k l ≤ M + M + 2 * K * M := by
  set Φ : S → S → ℝ := fun j k => spinVariation (c l j) k + spinVariation (c j l) k with hΦ
  have hΦ0 : ∀ j k, 0 ≤ Φ j k := fun j k => add_nonneg (spinVariation_nonneg _ _)
    (spinVariation_nonneg _ _)
  have hΦj : ∀ j, Summable (Φ j) := fun j => (hK l j).1.add (hK j l).1
  have hΦjsum : ∀ j, ∑' k, Φ j k ≤ 2 * K * γ l j := by
    intro j
    rw [(hK l j).1.tsum_add (hK j l).1]
    have := (hK l j).2; have := (hK j l).2
    rw [hγ_symm j l] at *
    linarith
  have hprod : Summable (Function.uncurry Φ) := by
    have hnn : 0 ≤ (fun p : S × S => Φ p.1 p.2) := fun p => hΦ0 _ _
    refine (summable_prod_of_nonneg hnn).2 ⟨hΦj, ?_⟩
    exact Summable.of_nonneg_of_le (fun j => tsum_nonneg (hΦ0 j)) hΦjsum
      ((hM l).1.mul_left (2 * K))
  have hΦk : ∀ k, Summable fun j => Φ j k := fun k =>
    summable_influence_row c γ hγ_nonneg hγ_symm M K hM hK l k
  have hsumk : Summable fun k => ∑' j, Φ j k := by
    have := hprod.prod_symm.prod
    exact this
  have hcolγ : Summable fun k => γ k l := ((hM l).1).congr fun k => hγ_symm l k
  have hcolγ' : ∑' k, γ k l ≤ M := by
    rw [show (fun k => γ k l) = γ l from funext fun k => hγ_symm k l]; exact (hM l).2
  have hsum : Summable (fun k => influenceMatrix c γ k l) :=
    (hcolγ.add (hM l).1).add hsumk
  refine ⟨hsum, ?_⟩
  have e : ∑' k, influenceMatrix c γ k l =
      ∑' k, γ k l + ∑' k, γ l k + ∑' k, ∑' j, Φ j k := by
    rw [← hcolγ.tsum_add (hM l).1, ← (hcolγ.add (hM l).1).tsum_add hsumk]
    rfl
  rw [e, hprod.tsum_comm' hΦj hΦk]
  have h3 : ∑' j, ∑' k, Φ j k ≤ 2 * K * M := by
    calc ∑' j, ∑' k, Φ j k ≤ ∑' j, 2 * K * γ l j :=
          (hprod.prod).tsum_le_tsum hΦjsum ((hM l).1.mul_left _)
      _ = 2 * K * ∑' j, γ l j := tsum_mul_left
      _ ≤ 2 * K * M := mul_le_mul_of_nonneg_left (hM l).2 (by linarith)
  have := (hM l).2
  linarith

include hγ_nonneg hγ_symm hM hK in
theorem finite_sum_le_influence (F : Finset S) (v : S → ℝ) (hv : ∀ l, 0 ≤ v l) (k : S) :
    ∑ j ∈ F, γ k j * v j + ∑ i ∈ F, γ i k * v i +
      ∑ i ∈ F, ∑ j ∈ F, spinVariation (c i j) k * (v i + v j) ≤
    ∑ l ∈ F, influenceMatrix c γ k l * v l := by
  have e : ∑ i ∈ F, ∑ j ∈ F, spinVariation (c i j) k * (v i + v j) =
      ∑ l ∈ F, (∑ j ∈ F, (spinVariation (c l j) k + spinVariation (c j l) k)) * v l := by
    simp only [mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
  rw [e, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  simp only [influenceMatrix]
  have := (summable_influence_row c γ hγ_nonneg hγ_symm M K hM hK l k).sum_le_tsum F
    (fun j _ => add_nonneg (spinVariation_nonneg _ _) (spinVariation_nonneg _ _))
  have hvl := hv l
  nlinarith

end InfluenceMatrix

theorem tsum_ite_prod_eq_sum_sum [DecidableEq S] (F : Finset S) (f : S → S → ℝ) :
    ∑' ij : S × S, (if ij.1 ∈ F ∧ ij.2 ∈ F then f ij.1 ij.2 else 0) =
      ∑ i ∈ F, ∑ j ∈ F, f i j := by
  rw [tsum_eq_sum (s := F ×ˢ F) (fun ij hij => by
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hij (Finset.mem_product.2 ⟨h1, h2⟩))]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos ⟨hi, hj⟩]

/-- The range condition for the exclusion operator on cylinder functions. -/
theorem exclusion_range_dense_aux
    (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η)
    (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdom : ∀ i j η, c i j η ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i)
    (hrows : ∃ M : ℝ, ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (hinfluence : ∃ K : ℝ, ∀ i j,
      Summable (spinVariation (c i j)) ∧
        (∑' k, spinVariation (c i j) k) ≤ K * γ i j) :
    ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) => r • fg.1 - fg.2) ''
        {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
          fg ∈ exclusionGraph c γ ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
            (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ}) := by
  classical
  obtain ⟨M, hM⟩ := hrows
  obtain ⟨K, hK⟩ := hinfluence
  set M0 := max M 0
  set K0 := max K 0
  have hM' : ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M0 :=
    fun i => ⟨(hM i).1, (hM i).2.trans (le_max_left _ _)⟩
  have hK' : ∀ i j, Summable (spinVariation (c i j)) ∧
      (∑' k, spinVariation (c i j) k) ≤ K0 * γ i j :=
    fun i j => ⟨(hK i j).1, (hK i j).2.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (hγ_nonneg i j))⟩
  have hM0 : 0 ≤ M0 := le_max_right _ _
  have hK0 : 0 ≤ K0 := le_max_right _ _
  set C := M0 + M0 + 2 * K0 * M0 with hCdef
  have hC : 0 ≤ C := by positivity
  set r := C + 1 with hrdef
  have hr : 0 < r := by linarith
  refine ⟨r, hr, ?_⟩
  rw [Metric.dense_iff]
  intro g ε hε
  -- approximate the target by a cylinder function
  obtain ⟨h, hball, Fh, hFh⟩ :=
    Metric.dense_iff.1 (dense_isCylinder (S := S)) g (ε / 2) (half_pos hε)
  set a : S → ℝ := fun k => spinVariation h k
  have ha0 : ∀ k, 0 ≤ a k := fun k => spinVariation_nonneg h k
  have has : Summable a := summable_of_ne_finset_zero (s := Fh)
    fun k hk => spinVariation_eq_zero_of_not_mem hFh hk
  -- the dominating sequence
  obtain ⟨w, hw0, hws, hdomw⟩ := exists_dominating_sequence (influenceMatrix c γ)
    (influenceMatrix_nonneg c γ hγ_nonneg hγ_symm M0 K0 hM' hK') C r hC (by linarith)
    (influenceMatrix_col c γ hγ_nonneg hγ_symm M0 K0 hM' hK' hK0) a ha0 has
  set ξ : S → Bool := fun _ => false
  set B : Finset S → S × S → ℝ := fun F ij =>
    (freezeDefect F ξ (c ij.1 ij.2) + (if ij.1 ∈ F ∧ ij.2 ∈ F then 0 else γ ij.1 ij.2)) *
      (w ij.1 + w ij.2) with hBdef
  have hfd_le : ∀ F i j, freezeDefect F ξ (c i j) ≤ γ i j := fun F i j =>
    freezeDefect_le F ξ (c i j) (γ i j) (hc_nonneg i j) (hdom i j)
  have hB0 : ∀ F ij, 0 ≤ B F ij := by
    intro F ij
    refine mul_nonneg (add_nonneg (freezeDefect_nonneg _ _ _) ?_)
      (add_nonneg (hw0 _) (hw0 _))
    split_ifs
    · exact le_rfl
    · exact hγ_nonneg _ _
  have hBle : ∀ F ij, B F ij ≤ 2 * (γ ij.1 ij.2 * (w ij.1 + w ij.2)) := by
    intro F ij
    have h1 := hfd_le F ij.1 ij.2
    have h2 : (if ij.1 ∈ F ∧ ij.2 ∈ F then (0 : ℝ) else γ ij.1 ij.2) ≤ γ ij.1 ij.2 := by
      split_ifs
      · exact hγ_nonneg _ _
      · exact le_rfl
    have hw := add_nonneg (hw0 ij.1) (hw0 ij.2)
    simp only [B]
    nlinarith
  have hbound_sum : Summable (fun ij : S × S => 2 * (γ ij.1 ij.2 * (w ij.1 + w ij.2))) :=
    (summable_gamma_mul_add γ hγ_nonneg hγ_symm M0 hM' w hw0 hws).mul_left 2
  have hBsum : ∀ F, Summable (B F) := fun F =>
    Summable.of_nonneg_of_le (hB0 F) (hBle F) hbound_sum
  have htend : Tendsto (fun F => ∑' ij, B F ij) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := B) (g := fun _ => (0 : ℝ))
      hbound_sum (fun ij => ?_) (Eventually.of_forall fun F ij => by
        rw [Real.norm_of_nonneg (hB0 F ij)]; exact hBle F ij)
    · simpa using this
    · have h1 := tendsto_freezeDefect ξ (c ij.1 ij.2)
      have h2 : Tendsto (fun F : Finset S =>
          (if ij.1 ∈ F ∧ ij.2 ∈ F then (0 : ℝ) else γ ij.1 ij.2)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({ij.1, ij.2} : Finset S)] with F hF
        rw [if_pos ⟨hF (by simp), hF (by simp)⟩]
      have := (h1.add h2).mul_const (w ij.1 + w ij.2)
      simpa [B] using this
  obtain ⟨F, hFsmall, hFh_le⟩ :=
    ((htend.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop Fh)).exists
  have hhF : ∀ η ζ : S → Bool, (∀ i ∈ F, η i = ζ i) → h η = h ζ :=
    fun η ζ hηζ => hFh η ζ fun i hi => hηζ i (hFh_le hi)
  -- solve the finite frozen system
  obtain ⟨u, huF, hu⟩ := exists_frozen_solution F ξ c hc_nonneg r hr h hhF
  set v : S → ℝ := fun k => spinVariation u k
  have hv0 : ∀ k, 0 ≤ v k := fun k => spinVariation_nonneg u k
  have hvF : ∀ k ∉ F, v k = 0 := fun k hk => spinVariation_eq_zero_of_not_mem huF hk
  have hest : ∀ k ∈ F, r * v k ≤ a k + ∑ l ∈ F, influenceMatrix c γ k l * v l := by
    intro k hk
    have h1 := frozen_variation_estimate F ξ c γ hc_nonneg hdom r hr.le h u hu k hk
    have h2 := finite_sum_le_influence c γ hγ_nonneg hγ_symm M0 K0 hM' hK' F v hv0 k
    simp only [v, a] at *
    linarith
  have hvw : ∀ k, v k ≤ w k := hdomw v F hv0 hvF hest
  -- the element of the graph
  obtain ⟨gu, hgu⟩ := exists_mem_exclusionGraph c γ hc_nonneg hdom u
    (summable_of_isCylinder γ hγ_nonneg hγ_symm ⟨M, hM⟩ u ⟨F, huF⟩)
  refine ⟨r • u - gu, ?_, (u, gu), ⟨hgu, F, huF⟩, rfl⟩
  -- the error estimate
  have herr : ‖r • u - gu - h‖ ≤ ∑' ij, B F ij := by
    refine (ContinuousMap.norm_le _ (tsum_nonneg (hB0 F))).2 fun η => ?_
    set Δ : S × S → ℝ := fun ij => u (exclusionExchange ij.1 ij.2 η) - u η
    have hΔ : ∀ ij, |Δ ij| ≤ w ij.1 + w ij.2 := fun ij =>
      (abs_exchange_le_spinVariation u ij.1 ij.2 η).trans (add_le_add (hvw _) (hvw _))
    set D : S × S → ℝ := fun ij =>
      (if ij.1 ∈ F ∧ ij.2 ∈ F then c ij.1 ij.2 (freeze F ξ η) * Δ ij else 0) -
        c ij.1 ij.2 η * Δ ij
    have hT : Summable (fun ij : S × S => c ij.1 ij.2 η * Δ ij) :=
      exclusion_series_summable c γ hc_nonneg hdom u hgu.1 η
    have hfin : Summable (fun ij : S × S =>
        if ij.1 ∈ F ∧ ij.2 ∈ F then c ij.1 ij.2 (freeze F ξ η) * Δ ij else 0) :=
      summable_of_ne_finset_zero (s := F ×ˢ F) fun ij hij => by
        rw [if_neg]; rintro ⟨h1, h2⟩; exact hij (Finset.mem_product.2 ⟨h1, h2⟩)
    have hval : (r • u - gu - h) η = ∑' ij, D ij := by
      have e1 := hu η
      have e2 := hgu.2 η
      have e3 := tsum_ite_prod_eq_sum_sum F
        (fun i j => c i j (freeze F ξ η) * (u (exclusionExchange i j η) - u η))
      simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
      rw [hfin.tsum_sub hT]
      simp only [Δ] at e3 ⊢
      rw [e3, ← e2]
      linarith
    rw [hval]
    refine tsum_of_norm_bounded (hBsum F).hasSum fun ij => ?_
    rw [Real.norm_eq_abs]
    have hw := add_nonneg (hw0 ij.1) (hw0 ij.2)
    by_cases hin : ij.1 ∈ F ∧ ij.2 ∈ F
    · have hD : D ij = (c ij.1 ij.2 (freeze F ξ η) - c ij.1 ij.2 η) * Δ ij := by
        simp only [D, if_pos hin]; ring
      have hB : B F ij = freezeDefect F ξ (c ij.1 ij.2) * (w ij.1 + w ij.2) := by
        simp only [B, if_pos hin, add_zero]
      rw [hD, hB, abs_mul]
      exact mul_le_mul (abs_sub_le_freezeDefect F ξ _ η) (hΔ ij) (abs_nonneg _)
        (freezeDefect_nonneg _ _ _)
    · have hD : D ij = -(c ij.1 ij.2 η * Δ ij) := by
        simp only [D, if_neg hin]; ring
      have hB : B F ij = (freezeDefect F ξ (c ij.1 ij.2) + γ ij.1 ij.2) *
          (w ij.1 + w ij.2) := by
        simp only [B, if_neg hin]
      rw [hD, hB, abs_neg, abs_mul, abs_of_nonneg (hc_nonneg _ _ _)]
      have := freezeDefect_nonneg F ξ (c ij.1 ij.2)
      calc c ij.1 ij.2 η * |Δ ij| ≤ γ ij.1 ij.2 * (w ij.1 + w ij.2) :=
            mul_le_mul (hdom _ _ _) (hΔ ij) (abs_nonneg _) (hγ_nonneg _ _)
        _ ≤ _ := by nlinarith
  rw [Metric.mem_ball, dist_eq_norm] at hball ⊢
  calc ‖r • u - gu - g‖ = ‖(r • u - gu - h) + (h - g)‖ := by congr 1; abel
    _ ≤ ‖r • u - gu - h‖ + ‖h - g‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (herr.trans hFsmall.le) hball
    _ = ε := add_halves ε

end Assembly

end EthierKurtz.ExclusionRangeProof

open EthierKurtz EthierKurtz.ExclusionRangeProof

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
    ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) => r • fg.1 - fg.2) ''
        {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
          fg ∈ exclusionGraph c γ ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
            (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ}) := by
  exact exclusion_range_dense_aux c γ hc_nonneg hγ_nonneg hdom hγ_symm hrows hinfluence
