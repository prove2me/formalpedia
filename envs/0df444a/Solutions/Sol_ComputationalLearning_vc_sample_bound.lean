-- Prove2me | solution 1 for ComputationalLearning.vc_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-29T11:50:17.292612+00:00
-- url     : https://prove2.me/submissions/db51e92f-08fb-40ce-a754-674bed104544

import Mathlib
import Definitions.Def_ComputationalLearning_VC

/-!
# Kearns and Vazirani, Theorems 3.3 and 3.4: the ε-net theorem and the VC sample bound
-/

open MeasureTheory

namespace ComputationalLearning

section Combinatorics

variable {X : Type*}

lemma phi_eq_sum_choose (d m : ℕ) : Phi d m = ∑ i ∈ Finset.range (d + 1), m.choose i := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => simp [Phi]
    | succ d => simp [Phi, Finset.sum_range_succ']
  | succ m ih =>
    cases d with
    | zero => simp [Phi]
    | succ d =>
      rw [show Phi (d + 1) (m + 1) = Phi (d + 1) m + Phi d m from rfl, ih (d + 1), ih d]
      rw [Finset.sum_range_succ' (fun i => (m + 1).choose i),
        Finset.sum_range_succ' (fun i => m.choose i) (d + 1)]
      simp only [Nat.choose_succ_succ, Finset.sum_add_distrib, Nat.choose_zero_right]
      ring

lemma phi_mono_right {d m m' : ℕ} (h : m ≤ m') : Phi d m ≤ Phi d m' := by
  rw [phi_eq_sum_choose, phi_eq_sum_choose]
  exact Finset.sum_le_sum fun i _ ↦ Nat.choose_le_choose i h

/-- Sauer's lemma for a single finite set. -/
lemma restrictions_ncard_le_phi (C : Set (X → Bool)) (d : ℕ) (hd : vcDim C ≤ d)
    (S : Finset X) : (restrictions C S).ncard ≤ Phi d S.card := by
  classical
  set F := restrictions C S with hF
  let tset : (S → Bool) → Finset S := fun f => Finset.univ.filter (fun x => f x = true)
  have hinj : Function.Injective tset := by
    intro f g hfg
    funext x
    have hx := congrArg (fun s : Finset S => x ∈ s) hfg
    simp only [tset, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at hx
    exact Bool.eq_iff_iff.mpr hx
  set 𝒜 : Finset (Finset S) := F.toFinset.image tset with h𝒜
  have hcard : F.ncard = 𝒜.card := by
    rw [h𝒜, Finset.card_image_of_injective _ hinj, Set.ncard_eq_toFinset_card']
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro t ht
    rw [Finset.mem_shatterer] at ht
    set T : Finset X := t.map (Function.Embedding.subtype _) with hT
    have hsh : Shatters C T := by
      intro f
      set u : Finset S := t.filter (fun y => if h : y ∈ t then
        f ⟨y.1, Finset.mem_map_of_mem (Function.Embedding.subtype _) h⟩ = true else False) with hu
      have hut : u ⊆ t := by rw [hu]; exact Finset.filter_subset _ t
      obtain ⟨v, hv𝒜, hvu⟩ := ht hut
      obtain ⟨g, hgF, rfl⟩ := Finset.mem_image.mp hv𝒜
      rw [Set.mem_toFinset] at hgF
      obtain ⟨c, hcC, hcg⟩ := hgF
      refine ⟨c, hcC, ?_⟩
      rintro ⟨x, hx⟩
      obtain ⟨y, hyt, rfl⟩ := Finset.mem_map.mp hx
      have key : y ∈ t ∩ tset g ↔ y ∈ u := by rw [hvu]
      simp only [Finset.mem_inter, tset, Finset.mem_filter, Finset.mem_univ, true_and, hu,
        dif_pos hyt] at key
      have hgy : g y = true ↔ f ⟨y.1, hx⟩ = true := by
        constructor
        · intro h; exact (key.mp ⟨hyt, h⟩).2
        · intro h; exact (key.mpr ⟨hyt, h⟩).2
      show c y.1 = f ⟨y.1, hx⟩
      rw [← hcg y]
      exact Bool.eq_iff_iff.mpr hgy
    have h1 : (T.card : ℕ∞) ≤ vcDim C :=
      le_iSup₂ (f := fun (S : Finset X) (_ : Shatters C S) => (S.card : ℕ∞)) T hsh
    have h2 : T.card = t.card := Finset.card_map _
    have h3 : (t.card : ℕ∞) ≤ d := by rw [← h2]; exact h1.trans hd
    exact_mod_cast h3
  calc F.ncard = 𝒜.card := hcard
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card S).choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card S).choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hvc)
    _ = Phi d S.card := by
        rw [phi_eq_sum_choose, Fintype.card_coe]
        congr 1
        ext k
        simp

/-- Swap the coordinates `i` with `σ i = true` between the two halves of a double sample. -/
def swapPair {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → X) × (Fin m → X)) :
    (Fin m → X) × (Fin m → X) :=
  (fun i ↦ if σ i then p.2 i else p.1 i, fun i ↦ if σ i then p.1 i else p.2 i)

open Classical in
/-- For a fixed error pattern `e`, few swaps put all errors in the second half and at least
`εm/2` of them. -/
lemma card_swaps_pattern_le {m : ℕ} (ε : ℝ) (e : X → Bool) (p : (Fin m → X) × (Fin m → X)) :
    (((Finset.univ.filter fun σ : Fin m → Bool ↦
        (∀ i, e ((swapPair σ p).1 i) = false) ∧
        ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ e ((swapPair σ p).2 i) = true).card : ℝ)).card
        : ℝ)) ≤ 2 ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by
  set G := Finset.univ.filter fun σ : Fin m → Bool ↦
        (∀ i, e ((swapPair σ p).1 i) = false) ∧
        ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ e ((swapPair σ p).2 i) = true).card : ℝ)
    with hG
  set K := Finset.univ.filter fun i : Fin m ↦ e (p.1 i) = true ∨ e (p.2 i) = true with hK
  have hsub : G ⊆ Fintype.piFinset (fun i ↦ if i ∈ K then {e (p.1 i)} else Finset.univ) := by
    intro σ hσ
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · have h1 := hσ.1 i
      simp only [swapPair] at h1
      rw [Finset.mem_singleton]
      rw [hK, Finset.mem_filter] at hi
      cases hσi : σ i
      · simp only [hσi, Bool.false_eq_true, ↓reduceIte] at h1
        rw [h1]
      · simp only [hσi, ↓reduceIte] at h1
        rcases hi.2 with h | h
        · exact h.symm
        · rw [h1] at h; exact absurd h Bool.false_ne_true
    · exact Finset.mem_univ _
  have hcardpi : (Fintype.piFinset (fun i ↦ if i ∈ K then {e (p.1 i)} else Finset.univ)).card
      = 2 ^ (m - K.card) := by
    rw [Fintype.card_piFinset]
    have : ∀ i, ((if i ∈ K then {e (p.1 i)} else Finset.univ : Finset Bool)).card =
        if i ∈ K then 1 else 2 := by
      intro i; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp [Finset.filter_mem_eq_inter]
  rcases G.eq_empty_or_nonempty with hemp | ⟨σ, hσ⟩
  · rw [hemp, Finset.card_empty, Nat.cast_zero]
    positivity
  have hKge : ε * m / 2 ≤ (K.card : ℝ) := by
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine hσ.2.trans ?_
    have hsubK : (Finset.univ.filter fun i ↦ e ((swapPair σ p).2 i) = true) ⊆ K := by
      intro i hi'
      rw [Finset.mem_filter] at hi'
      have hi : e (if σ i then p.1 i else p.2 i) = true := hi'.2
      rw [hK, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hσi : σ i = true
      · rw [if_pos hσi] at hi
        exact Or.inl hi
      · rw [if_neg hσi] at hi
        exact Or.inr hi
    exact_mod_cast Finset.card_le_card hsubK
  have hKm : K.card ≤ m := by
    simpa using Finset.card_le_univ K
  calc (G.card : ℝ) ≤ ((2 ^ (m - K.card) : ℕ) : ℝ) := by
        rw [← hcardpi]; exact_mod_cast Finset.card_le_card hsub
    _ = 2 ^ m * (2 : ℝ) ^ (-(K.card : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat,
          pow_sub₀ _ (by norm_num) hKm]
    _ ≤ 2 ^ m * (2 : ℝ) ^ (-(ε * m / 2)) := by
        gcongr
        · norm_num

open Classical in
/-- The combinatorial core of the random-partition argument. -/
lemma card_swaps_le (H : Set (X → Bool)) (c : X → Bool) (d : ℕ) (hd : vcDim H ≤ d) (ε : ℝ)
    (m : ℕ) (p : (Fin m → X) × (Fin m → X)) :
    (((Finset.univ.filter fun σ : Fin m → Bool ↦
        swapPair σ p ∈ doubleSampleEvent H c ε m).card : ℝ)) ≤
      Phi d (2 * m) * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
  set S : Finset X := Finset.univ.image p.1 ∪ Finset.univ.image p.2 with hS
  have hS1 : ∀ σ : Fin m → Bool, ∀ i, (swapPair σ p).1 i ∈ S := by
    intro σ i
    simp only [swapPair, hS, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    split_ifs
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
  have hS2 : ∀ σ : Fin m → Bool, ∀ i, (swapPair σ p).2 i ∈ S := by
    intro σ i
    simp only [swapPair, hS, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    split_ifs
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, rfl⟩
  have hScard : S.card ≤ 2 * m := by
    calc S.card ≤ (Finset.univ.image p.1).card + (Finset.univ.image p.2).card :=
          Finset.card_union_le _ _
      _ ≤ m + m := by
          gcongr <;> exact Finset.card_image_le.trans (by simp)
      _ = 2 * m := by ring
  set R := (restrictions H S).toFinset with hR
  let ef : (S → Bool) → X → Bool := fun f x ↦ if hx : x ∈ S then f ⟨x, hx⟩ != c x else false
  have hsub : (Finset.univ.filter fun σ : Fin m → Bool ↦
      swapPair σ p ∈ doubleSampleEvent H c ε m) ⊆ R.biUnion (fun f ↦
        Finset.univ.filter fun σ : Fin m → Bool ↦
        (∀ i, ef f ((swapPair σ p).1 i) = false) ∧
        ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ ef f ((swapPair σ p).2 i) = true).card : ℝ)) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, doubleSampleEvent,
      Set.mem_setOf_eq] at hσ
    obtain ⟨h, hH, h1, h2⟩ := hσ
    rw [Finset.mem_biUnion]
    refine ⟨fun x ↦ h x, ?_, ?_⟩
    · rw [hR, Set.mem_toFinset]
      exact ⟨h, hH, fun x ↦ rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i ↦ ?_, ?_⟩
      · simp only [ef, dif_pos (hS1 σ i), h1 i, bne_self_eq_false]
      · refine h2.trans (le_of_eq ?_)
        congr 2
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ef, dif_pos (hS2 σ i),
          bne_iff_ne]
  have hRcard : (R.card : ℝ) ≤ Phi d (2 * m) := by
    rw [hR, ← Set.ncard_eq_toFinset_card']
    exact_mod_cast (restrictions_ncard_le_phi H d hd S).trans (phi_mono_right hScard)
  calc _ ≤ ((R.biUnion (fun f ↦
        Finset.univ.filter fun σ : Fin m → Bool ↦
        (∀ i, ef f ((swapPair σ p).1 i) = false) ∧
        ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ ef f ((swapPair σ p).2 i) = true).card : ℝ))).card
          : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ f ∈ R, (((Finset.univ.filter fun σ : Fin m → Bool ↦
        (∀ i, ef f ((swapPair σ p).1 i) = false) ∧
        ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ ef f ((swapPair σ p).2 i) = true).card : ℝ)).card
          : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ f ∈ R, (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2))) :=
        Finset.sum_le_sum fun f _ ↦ card_swaps_pattern_le ε (ef f) p
    _ = R.card * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Phi d (2 * m) * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2))) := by
        gcongr

end Combinatorics

section Measure

variable {X : Type*} [MeasurableSpace X]

lemma swapPair_measurePreserving (D : Measure X) [IsProbabilityMeasure D] {m : ℕ}
    (σ : Fin m → Bool) :
    MeasurePreserving (swapPair σ)
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D)) := by
  have he := measurePreserving_arrowProdEquivProdArrow X X (Fin m) (fun _ ↦ D) (fun _ ↦ D)
  have hg : MeasurePreserving
      (fun (a : Fin m → X × X) i ↦ (if σ i then Prod.swap else id) (a i))
      (Measure.pi fun _ : Fin m ↦ D.prod D) (Measure.pi fun _ : Fin m ↦ D.prod D) := by
    refine measurePreserving_pi _ _ fun i ↦ ?_
    split_ifs
    · exact Measure.measurePreserving_swap
    · exact MeasurePreserving.id _
  have hcomp := he.comp (hg.comp he.symm)
  convert hcomp using 1
  funext q
  ext i <;>
  · simp only [swapPair, Function.comp_apply, MeasurableEquiv.arrowProdEquivProdArrow,
      MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk,
      MeasurableEquiv.symm_mk, Equiv.coe_fn_symm_mk]
    split_ifs <;> rfl

/-- The random-partition bound `Pr[B] ≤ Φ_d(2m) 2^{-εm/2}`. -/
lemma doubleSample_measure_le (H : Set (X → Bool)) (c : X → Bool) (d : ℕ) (hd : vcDim H ≤ d)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ)
    (hnm : NullMeasurableSet (doubleSampleEvent H c ε m)
      ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))) :
    ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
        (doubleSampleEvent H c ε m) ≤
      ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
  classical
  set ν := (Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D) with hν
  set E := doubleSampleEvent H c ε m with hE
  have hpre : ∀ σ : Fin m → Bool, ν (swapPair σ ⁻¹' E) = ν E := fun σ ↦
    (swapPair_measurePreserving D σ).measure_preimage hnm
  have hnm' : ∀ σ : Fin m → Bool, NullMeasurableSet (swapPair σ ⁻¹' E) ν := fun σ ↦
    hnm.preimage (swapPair_measurePreserving D σ).quasiMeasurePreserving
  have hsum : ∑ σ : Fin m → Bool, ν (swapPair σ ⁻¹' E) =
      ∫⁻ q, ∑ σ : Fin m → Bool, (swapPair σ ⁻¹' E).indicator 1 q ∂ν := by
    have hae : ∀ σ ∈ (Finset.univ : Finset (Fin m → Bool)),
        AEMeasurable ((swapPair σ ⁻¹' E).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal)) ν :=
      fun σ _ ↦ (aemeasurable_indicator_iff₀ (hnm' σ)).mpr aemeasurable_const
    rw [lintegral_finset_sum' _ hae]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [lintegral_indicator_one₀ (hnm' σ)]
  have hpt : ∀ q, ∑ σ : Fin m → Bool, (swapPair σ ⁻¹' E).indicator 1 q ≤
      ENNReal.ofReal (Phi d (2 * m) * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2)))) := by
    intro q
    have : ∑ σ : Fin m → Bool, (swapPair σ ⁻¹' E).indicator (1 : (Fin m → X) × (Fin m → X) → ENNReal) q =
        ((Finset.univ.filter fun σ : Fin m → Bool ↦ swapPair σ q ∈ E).card : ENNReal) := by
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
      rw [Finset.sum_boole]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_swaps_le H c d hd ε m q)
  have h2m : (2 : ENNReal) ^ m * ν E ≤
      (2 : ENNReal) ^ m * ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
    calc (2 : ENNReal) ^ m * ν E = ∑ σ : Fin m → Bool, ν (swapPair σ ⁻¹' E) := by
          simp only [hpre, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ ∫⁻ _q, ENNReal.ofReal (Phi d (2 * m) * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2)))) ∂ν := by
          rw [hsum]; exact lintegral_mono hpt
      _ = ENNReal.ofReal (Phi d (2 * m) * (2 ^ m * (2 : ℝ) ^ (-(ε * m / 2)))) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ = (2 : ENNReal) ^ m * ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
          rw [mul_left_comm, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).mp h2m

/-- A region of weight at least `ε` is hit at least `εm/2` times with probability at least
`1/2` once `m ≥ 8/ε`. -/
lemma count_hits_ge_half (D : Measure X) [IsProbabilityMeasure D] {A : Set X}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) (hDA : ENNReal.ofReal ε ≤ D A) (m : ℕ)
    (hm : 8 / ε ≤ m) :
    (1 / 2 : ENNReal) ≤ (Measure.pi fun _ : Fin m ↦ D)
      {y | ε * m / 2 ≤ ((Finset.univ.filter fun i ↦ y i ∈ A).card : ℝ)} := by
  set μ := Measure.pi fun _ : Fin m ↦ D with hμ
  set N : (Fin m → X) → ℕ := fun y ↦ (Finset.univ.filter fun i ↦ y i ∈ A).card with hN
  set g : X → ℝ := fun x ↦ if x ∈ A then 1 / 2 else 1 with hg
  set F : (Fin m → X) → ℝ := fun y ↦ ∏ i, g (y i) with hFdef
  have hF : ∀ y, F y = (1 / 2 : ℝ) ^ N y := by
    intro y
    simp only [F, g, N]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hgm : Measurable g := Measurable.ite hA measurable_const measurable_const
  have hFm : Measurable F := Finset.measurable_prod _ fun i _ ↦ hgm.comp (measurable_pi_apply i)
  have hFint : Integrable F μ := Integrable.of_bound hFm.aestronglyMeasurable 1
    (ae_of_all _ fun y ↦ by
      rw [hF, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (by norm_num) (by norm_num))
  have hint_g : ∫ x, g x ∂D = 1 - D.real A / 2 := by
    have : g = fun x ↦ 1 - A.indicator (fun _ ↦ (1 / 2 : ℝ)) x := by
      funext x; simp only [g, Set.indicator_apply]; split_ifs <;> norm_num
    rw [this, integral_sub (integrable_const _) ((integrable_const _).indicator hA),
      integral_const, integral_indicator_const _ hA]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  have hintF : ∫ y, F y ∂μ = (1 - D.real A / 2) ^ m := by
    rw [hFdef, hμ, integral_fintype_prod_eq_prod (fun _ ↦ g), hint_g, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hp : ε ≤ D.real A := by
    rw [measureReal_def]; exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hDA
  have hp1 : D.real A ≤ 1 := measureReal_le_one
  set a := ε * m / 2 with ha_def
  have ha : 4 ≤ a := by
    have : 8 ≤ ε * m := by rw [div_le_iff₀ hε] at hm; linarith
    linarith
  have hbound : (1 - D.real A / 2) ^ m ≤ Real.exp (-a) := by
    calc (1 - D.real A / 2) ^ m ≤ (Real.exp (-(D.real A / 2))) ^ m :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) m
      _ = Real.exp (-(D.real A / 2) * m) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by
          rw [ha_def]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith)
  set t : ℝ := (2 : ℝ) ^ (-a) with ht
  have htpos : 0 < t := by positivity
  have hsub : {y | ¬ (a ≤ (N y : ℝ))} ⊆ {y | t ≤ F y} := by
    intro y hy
    simp only [Set.mem_setOf_eq, not_le] at hy ⊢
    rw [hF, one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun y ↦ by rw [hF]; positivity) hFint t
  rw [hintF] at hmarkov
  have hnum : Real.exp (-a) / t ≤ 1 / 2 := by
    rw [ht, Real.rpow_neg (by norm_num), div_inv_eq_mul, Real.rpow_def_of_pos (by norm_num),
      ← Real.exp_add]
    have hl := Real.log_two_lt_d9
    have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc Real.exp (-a + Real.log 2 * a) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  have hreal : μ.real {y | t ≤ F y} ≤ 1 / 2 := by
    refine le_trans ?_ hnum
    rw [le_div_iff₀ htpos, mul_comm]
    linarith
  have hcompl : μ {y | ¬ (a ≤ (N y : ℝ))} ≤ 1 / 2 := by
    calc μ {y | ¬ (a ≤ (N y : ℝ))} ≤ μ {y | t ≤ F y} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {y | t ≤ F y}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
      _ = 1 / 2 := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
            one_div]
  have htot : (1 : ENNReal) ≤ μ {y | a ≤ (N y : ℝ)} + μ {y | ¬ (a ≤ (N y : ℝ))} := by
    rw [← measure_univ (μ := μ)]
    calc μ Set.univ = μ ({y | a ≤ (N y : ℝ)} ∪ {y | ¬ (a ≤ (N y : ℝ))}) := by
          congr 1; ext y; simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]; exact _root_.em _
      _ ≤ _ := measure_union_le _ _
  have h2 : (1 : ENNReal) ≤ μ {y | a ≤ (N y : ℝ)} + 1 / 2 := htot.trans (by gcongr)
  rw [← tsub_le_iff_right, one_div, ENNReal.one_sub_inv_two] at h2
  rw [one_div]
  exact h2

/-- The reduction `Pr[A] ≤ 2 Pr[B]`. -/
lemma badSample_le_two_mul (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h) (c : X → Bool)
    (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) (m : ℕ)
    (hm : 8 / ε ≤ m) :
    (Measure.pi fun _ : Fin m ↦ D)
        {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)} ≤
      2 * ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
        (doubleSampleEvent H c ε m) := by
  set μ := Measure.pi fun _ : Fin m ↦ D with hμ
  set ν := μ.prod μ with hν
  set E := doubleSampleEvent H c ε m with hE
  set E' := toMeasurable ν E with hE'
  have hE'm : MeasurableSet E' := measurableSet_toMeasurable ν E
  set f : (Fin m → X) → ENNReal := fun x ↦ μ (Prod.mk x ⁻¹' E') with hf
  have hfm : Measurable f := measurable_measure_prodMk_left hE'm
  have hνE : ν E = ∫⁻ x, f x ∂μ := by
    rw [← measure_toMeasurable E, hν, Measure.prod_apply hE'm]
  have hsub : {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)} ⊆
      {x | 1 / 2 ≤ f x} := by
    rintro x ⟨h, hH, hDh, hcons⟩
    have hAm : MeasurableSet (errorRegion c h) :=
      (measurableSet_eq_fun (hHm h hH) hc).compl
    let _ : DecidablePred (· ∈ errorRegion c h) := fun x ↦
      inferInstanceAs (Decidable (h x ≠ c x))
    refine (count_hits_ge_half D hAm hε hDh m hm).trans (measure_mono ?_)
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    simp only [Set.mem_preimage]
    apply subset_toMeasurable
    exact ⟨h, hH, hcons, hy⟩
  calc μ {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)}
      ≤ μ {x | 1 / 2 ≤ f x} := measure_mono hsub
    _ ≤ (∫⁻ x, f x ∂μ) / (1 / 2) :=
        meas_ge_le_lintegral_div hfm.aemeasurable (by simp) (by simp)
    _ = 2 * ν E := by
        rw [hνE, ENNReal.div_eq_inv_mul, one_div, inv_inv]

/-- Transfer from labeled samples to unlabeled ones. -/
lemma sampleLaw_le_of_labeled (D : Measure X) [IsProbabilityMeasure D] (c : X → Bool)
    (hc : Measurable c) (m : ℕ) (s : Set (Fin m → X × Bool)) (B : Set (Fin m → X))
    (hs : ∀ S ∈ s, IsLabeledBy c S → (fun i ↦ (S i).1) ∈ B) :
    sampleLaw D c m s ≤ (Measure.pi fun _ : Fin m ↦ D) B := by
  set μ := Measure.pi fun _ : Fin m ↦ D with hμ
  have hφ : Measurable (fun x : X ↦ (x, c x)) := measurable_id.prodMk hc
  haveI : IsProbabilityMeasure (D.map fun x : X ↦ (x, c x)) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  set Φ : (Fin m → X) → (Fin m → X × Bool) := fun x i ↦ (x i, c (x i)) with hΦ
  have hΦm : Measurable Φ := measurable_pi_lambda _ fun i ↦ hφ.comp (measurable_pi_apply i)
  have hlaw : sampleLaw D c m = μ.map Φ := by
    rw [sampleLaw, exampleLaw, hμ, hΦ,
      Measure.pi_map_pi (f := fun _ ↦ fun x : X ↦ (x, c x)) (fun _ ↦ hφ.aemeasurable)]
  set g : (Fin m → X × Bool) → (Fin m → X) := fun S i ↦ (S i).1 with hg
  have hgm : Measurable g := measurable_pi_lambda _ fun i ↦ measurable_fst.comp
    (measurable_pi_apply i)
  set T := toMeasurable μ B with hT
  set L := {S : Fin m → X × Bool | ¬ IsLabeledBy c S} with hL
  have hLm : MeasurableSet L := by
    have hLeq : L = (⋂ i, {S : Fin m → X × Bool | (S i).2 = c (S i).1})ᶜ := by
      ext S; simp [hL, IsLabeledBy]
    rw [hLeq]
    refine MeasurableSet.compl ?_
    exact MeasurableSet.iInter fun i ↦ measurableSet_eq_fun
      (measurable_snd.comp (measurable_pi_apply i)) (hc.comp (measurable_fst.comp
        (measurable_pi_apply i)))
  have hsub : s ⊆ g ⁻¹' T ∪ L := by
    intro S hS
    by_cases hlab : IsLabeledBy c S
    · exact Or.inl (subset_toMeasurable μ B (hs S hS hlab))
    · exact Or.inr hlab
  have hpre1 : Φ ⁻¹' (g ⁻¹' T) = T := by
    ext x; simp [hΦ, hg]
  have hpre2 : Φ ⁻¹' L = ∅ := by
    ext x; simp [hΦ, hL, IsLabeledBy]
  rw [hlaw]
  calc μ.map Φ s ≤ μ.map Φ (g ⁻¹' T ∪ L) := measure_mono hsub
    _ ≤ μ.map Φ (g ⁻¹' T) + μ.map Φ L := measure_union_le _ _
    _ = μ T + μ ∅ := by
        rw [Measure.map_apply hΦm (hgm (measurableSet_toMeasurable μ B)), hpre1,
          Measure.map_apply hΦm hLm, hpre2]
    _ = μ B := by rw [measure_empty, add_zero, hT, measure_toMeasurable]

lemma not_isEpsNet_iff (H : Set (X → Bool)) (c : X → Bool) (D : Measure X) (ε : ℝ) {m : ℕ}
    (S : Fin m → X × Bool) :
    ¬ IsEpsNet H c D ε (samplePoints S) ↔
      ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (S i).1 = c (S i).1 := by
  classical
  simp only [IsEpsNet, samplePoints, not_forall, not_exists, not_and, exists_prop,
    Finset.mem_image, Finset.mem_univ, true_and, errorRegion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hH, hD, hno⟩
    refine ⟨h, hH, hD, fun i ↦ ?_⟩
    by_contra hne
    exact hno _ ⟨i, rfl⟩ hne
  · rintro ⟨h, hH, hD, hall⟩
    refine ⟨h, hH, hD, ?_⟩
    rintro x ⟨i, rfl⟩ hne
    exact hne (hall i)

/-- The bad event `A` of the proof, on unlabeled samples, bounded by `2 Φ_d(2m) 2^{-εm/2}`. -/
lemma badSample_le_bound (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h) (d : ℕ)
    (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c) (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : 8 / ε ≤ m) :
    (Measure.pi fun _ : Fin m ↦ D)
        {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)} ≤
      ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
  calc _ ≤ 2 * ((Measure.pi fun _ : Fin m ↦ D).prod (Measure.pi fun _ : Fin m ↦ D))
        (doubleSampleEvent H c ε m) := badSample_le_two_mul H hHm c hc D hε m hm
    _ ≤ 2 * ENNReal.ofReal (Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
        gcongr
        exact doubleSample_measure_le H c d hd D ε m (hwb D inferInstance ε m)
    _ = ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
        rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-- Part (1): the ε-net bound. -/
lemma epsNet_failure_le (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h) (d : ℕ)
    (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c) (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) (m : ℕ) (hm : 8 / ε ≤ m) :
    sampleLaw D c m {S | ¬ IsEpsNet H c D ε (samplePoints S)} ≤
      ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) := by
  refine (sampleLaw_le_of_labeled D c hc m _ _ ?_).trans
    (badSample_le_bound H hHm d hd c hc hwb D hε m hm)
  intro S hS _
  exact (not_isEpsNet_iff H c D ε S).mp hS

/-- A consistent hypothesis of error greater than `ε` witnesses the bad event. -/
lemma learner_failure_le_bad (H : Set (X → Bool)) (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ)
    (L : (Fin m → X × Bool) → X → Bool) (hLH : ∀ S, L S ∈ H)
    (hLc : ∀ S, IsLabeledBy c S → IsConsistent (L S) S) :
    sampleLaw D c m {S | ε < errorOf D c (L S)} ≤
      (Measure.pi fun _ : Fin m ↦ D)
        {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)} := by
  refine sampleLaw_le_of_labeled D c hc m _ _ ?_
  intro S hS hlab
  refine ⟨L S, hLH S, ?_, fun i ↦ ?_⟩
  · have hS' : ε < errorOf D c (L S) := hS
    rw [errorOf] at hS'
    rw [errorRegion, ← ENNReal.ofReal_toReal (measure_ne_top D _)]
    exact ENNReal.ofReal_le_ofReal hS'.le
  · rw [hLc S hlab i, hlab i]

omit [MeasurableSpace X] in
/-- The case `d = 0`: a class of VC dimension `0` has at most one hypothesis. -/
lemma vcDim_zero_subsingleton (H : Set (X → Bool)) (hd : vcDim H ≤ (0 : ℕ)) :
    H.Subsingleton := by
  intro h1 hh1 h2 hh2
  by_contra hne
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  have hsh : Shatters H {x} := by
    intro f
    have hx' : x ∈ ({x} : Finset X) := Finset.mem_singleton_self x
    by_cases hf : f ⟨x, hx'⟩ = h1 x
    · refine ⟨h1, hh1, ?_⟩
      rintro ⟨y, hy⟩
      rw [Finset.mem_singleton] at hy
      subst hy
      exact hf.symm
    · refine ⟨h2, hh2, ?_⟩
      rintro ⟨y, hy⟩
      rw [Finset.mem_singleton] at hy
      subst hy
      cases h : f ⟨y, hx'⟩ <;> cases h1y : h1 y <;> cases h2y : h2 y <;> simp_all
  have h1le : ((({x} : Finset X)).card : ℕ∞) ≤ vcDim H :=
    le_iSup₂ (f := fun (S : Finset X) (_ : Shatters H S) => (S.card : ℕ∞)) {x} hsh
  rw [Finset.card_singleton] at h1le
  have := h1le.trans hd
  norm_num at this

lemma badSample_le_of_subsingleton (H : Set (X → Bool)) (hH0 : H.Subsingleton)
    (c : X → Bool) (hc : Measurable c) (hHm : ∀ h ∈ H, Measurable h) (D : Measure X)
    [IsProbabilityMeasure D] (ε : ℝ) (m : ℕ) :
    (Measure.pi fun _ : Fin m ↦ D)
        {x | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧ ∀ i, h (x i) = c (x i)} ≤
      ENNReal.ofReal (Real.exp (-(ε * m))) := by
  by_cases hex : ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h)
  · obtain ⟨h0, hh0, hD0⟩ := hex
    have hAm : MeasurableSet (errorRegion c h0) :=
      (measurableSet_eq_fun (hHm h0 hh0) hc).compl
    have hsub : {x : Fin m → X | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧
        ∀ i, h (x i) = c (x i)} ⊆ Set.univ.pi fun _ ↦ (errorRegion c h0)ᶜ := by
      rintro x ⟨h, hH, -, hcons⟩
      obtain rfl := hH0 hH hh0
      intro i _
      simp [errorRegion, hcons i]
    refine (measure_mono hsub).trans ?_
    rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hp : ε ≤ D.real (errorRegion c h0) := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hD0
    have hcomp : D (errorRegion c h0)ᶜ = ENNReal.ofReal (1 - D.real (errorRegion c h0)) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top D _), ← measureReal_def,
        probReal_compl_eq_one_sub hAm]
    rw [hcomp, ← ENNReal.ofReal_pow (by
      have : D.real (errorRegion c h0) ≤ 1 := measureReal_le_one
      linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0le : 0 ≤ 1 - D.real (errorRegion c h0) := by
      have : D.real (errorRegion c h0) ≤ 1 := measureReal_le_one
      linarith
    calc (1 - D.real (errorRegion c h0)) ^ m ≤ (Real.exp (-ε)) ^ m :=
          pow_le_pow_left₀ h0le ((by linarith : 1 - D.real (errorRegion c h0) ≤ 1 - ε).trans
            (Real.one_sub_le_exp_neg ε)) m
      _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
  · have hemp : {x : Fin m → X | ∃ h ∈ H, ENNReal.ofReal ε ≤ D (errorRegion c h) ∧
        ∀ i, h (x i) = c (x i)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, hH, hD, -⟩
      exact hex ⟨h, hH, hD⟩
    rw [hemp, measure_empty]
    exact bot_le

end Measure

section Numerics

lemma phi_le_pow (d m : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    (Phi d m : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hmR : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
  have hdm' : (d:ℝ) ≤ m := by exact_mod_cast hdm
  set r : ℝ := d / m with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hmR]; exact hdm'
  have hrd : 0 < r ^ d := pow_pos hr0 d
  rw [phi_eq_sum_choose]
  push_cast
  have step1 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) ≤
      (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := by
    rw [le_div_iff₀ hrd, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.mem_range] at hi
    have : r ^ d ≤ r ^ i := pow_le_pow_of_le_one hr0.le hr1 (by omega)
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have step2 : ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    intro i _ _
    positivity
  have step3 : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i = (r + 1) ^ m := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, mul_comm]
  have step4 : (r + 1) ^ m ≤ Real.exp d := by
    calc (r + 1) ^ m ≤ (Real.exp r) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) m
      _ = Real.exp (m * r) := by rw [← Real.exp_nat_mul]
      _ = Real.exp d := by rw [hr]; congr 1; field_simp
  have step5 : Real.exp d / r ^ d = (Real.exp 1 * m / d) ^ d := by
    rw [show Real.exp d = Real.exp 1 ^ d by rw [← Real.exp_nat_mul, mul_one], hr, div_pow,
      mul_div_assoc, mul_pow, div_pow]
    field_simp
  calc ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)
      ≤ (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * r ^ i) / r ^ d := step1
    _ ≤ (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * r ^ i) / r ^ d :=
        div_le_div_of_nonneg_right step2 hrd.le
    _ = (r + 1) ^ m / r ^ d := by rw [step3]
    _ ≤ Real.exp d / r ^ d := div_le_div_of_nonneg_right step4 hrd.le
    _ = (Real.exp 1 * m / d) ^ d := step5

lemma key_log_ineq {ε u : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hu : 8 * (Real.log (13 / ε) / Real.log 2) / ε ≤ u) :
    Real.log (2 * Real.exp 1 * u) ≤ ε * u / 4 * Real.log 2 := by
  set w := 13 / ε with hw
  have hw13 : 13 < w := by rw [hw, lt_div_iff₀ hε]; linarith
  have hεw : ε = 13 / w := by rw [hw]; field_simp
  set ℓ := Real.log w with hℓ
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hlog13 : Real.log 13 ≤ 4 * Real.log 2 - 3 / 16 := by
    have h1 : Real.log 13 = Real.log 16 + Real.log (13 / 16) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 16 by norm_num)
    linarith
  have hlog13pos : 2 < Real.log 13 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith
  have hℓ13 : Real.log 13 < ℓ := Real.log_lt_log (by norm_num) hw13
  have hℓup : ℓ ≤ Real.log 13 + w / 13 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < w / 13 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hl2pos : 0 < Real.log 2 := by linarith
  have hℓpos : 0 < ℓ := by linarith
  set u0 := 8 * ℓ / (ε * Real.log 2) with hu0
  have hu0' : u0 = 8 * (Real.log (13 / ε) / Real.log 2) / ε := by
    rw [hu0, hℓ, hw]; field_simp
  rw [← hu0'] at hu
  have hu0pos : 0 < u0 := by positivity
  have hupos : 0 < u := lt_of_lt_of_le hu0pos hu
  have hsplit : Real.log (2 * Real.exp 1 * u) =
      Real.log (2 * Real.exp 1 * u0) + Real.log (u / u0) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hratio : Real.log (u / u0) ≤ u / u0 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hbase : Real.log (2 * Real.exp 1 * u0) ≤ 2 * ℓ := by
    have hle : 2 * Real.exp 1 * u0 ≤ w ^ 2 := by
      have heq : 2 * Real.exp 1 * u0 = 16 * Real.exp 1 * ℓ * w / (13 * Real.log 2) := by
        rw [hu0, hεw]; field_simp; ring
      rw [heq, div_le_iff₀ (by positivity)]
      have : 16 * Real.exp 1 * ℓ ≤ 13 * Real.log 2 * w := by nlinarith
      have hw0 : 0 < w := by linarith
      nlinarith
    calc Real.log (2 * Real.exp 1 * u0) ≤ Real.log (w ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * ℓ := by rw [Real.log_pow, hℓ]; push_cast; ring
  have hlin : u / u0 - 1 ≤ ε * (u - u0) / 4 * Real.log 2 := by
    have : u / u0 - 1 = (u - u0) * (ε * Real.log 2) / (8 * ℓ) := by
      rw [hu0]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    have hd : 0 ≤ (u - u0) * (ε * Real.log 2) := by
      have := sub_nonneg.mpr hu; positivity
    nlinarith
  have hu0val : ε * u0 / 4 * Real.log 2 = 2 * ℓ := by
    rw [hu0]; field_simp; ring
  nlinarith

lemma one_le_logb_thirteen {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : 1 ≤ Real.logb 2 (13 / ε) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one, le_div_iff₀ hε]
  linarith

lemma numeric_bound {d : ℕ} (hd : 1 ≤ d) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    {m : ℕ} (h1 : 4 / ε * Real.logb 2 (2 / δ) ≤ m)
    (h2 : 8 * d / ε * Real.logb 2 (13 / ε) ≤ m) :
    2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)) ≤ δ := by
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL13 := one_le_logb_thirteen hε hε1
  have hm8 : 8 * (d : ℝ) ≤ m := by
    have : 8 * (d : ℝ) / ε ≤ 8 * d / ε * Real.logb 2 (13 / ε) :=
      le_mul_of_one_le_right (by positivity) hL13
    have h8 : 8 * (d : ℝ) ≤ 8 * d / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    linarith
  have hdm : d ≤ 2 * m := by
    have : (d : ℝ) ≤ 2 * m := by linarith
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have hu : 8 * (Real.log (13 / ε) / Real.log 2) / ε ≤ (m : ℝ) / d := by
    rw [le_div_iff₀ hdpos, Real.log_div_log]
    calc 8 * Real.logb 2 (13 / ε) / ε * d = 8 * d / ε * Real.logb 2 (13 / ε) := by ring
      _ ≤ m := h2
  have hkey := key_log_ineq hε hε1 hu
  have hX : (Real.exp 1 * ((2 * m : ℕ) : ℝ) / d) ^ d ≤ Real.exp (ε * m / 4 * Real.log 2) := by
    have hpos : 0 < Real.exp 1 * ((2 * m : ℕ) : ℝ) / d := by push_cast; positivity
    rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : Real.exp 1 * ((2 * m : ℕ) : ℝ) / d = 2 * Real.exp 1 * ((m : ℝ) / d) := by
      push_cast; ring
    rw [this]
    calc (d : ℝ) * Real.log (2 * Real.exp 1 * ((m : ℝ) / d)) ≤
          d * (ε * ((m : ℝ) / d) / 4 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hkey hdpos.le
      _ = ε * m / 4 * Real.log 2 := by field_simp
  have hδ' : Real.log (2 / δ) ≤ ε * m / 4 * Real.log 2 := by
    have : Real.logb 2 (2 / δ) ≤ ε * m / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1; linarith
    rw [← Real.log_div_log, div_le_iff₀ hl2pos] at this
    linarith
  have h2pow : (2 : ℝ) ^ (-(ε * m / 2)) = Real.exp (-(ε * m / 2) * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hP' : (Phi d (2 * m) : ℝ) ≤ Real.exp (ε * m / 4 * Real.log 2) :=
    (phi_le_pow d (2 * m) hd hdm).trans hX
  calc 2 * (Phi d (2 * m) : ℝ) * (2 : ℝ) ^ (-(ε * m / 2)) ≤
        2 * Real.exp (ε * m / 4 * Real.log 2) * Real.exp (-(ε * m / 2) * Real.log 2) := by
        rw [h2pow]; gcongr
    _ = 2 * Real.exp (-(ε * m / 4 * Real.log 2)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 2 * Real.exp (-Real.log (2 / δ)) := by gcongr
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

lemma numeric_bound_zero {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) {m : ℕ}
    (h1 : 4 / ε * Real.logb 2 (2 / δ) ≤ m) : Real.exp (-(ε * m)) ≤ δ := by
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2lt : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hpos : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hlogb : Real.log (2 / δ) ≤ Real.logb 2 (2 / δ) := by
    rw [← Real.log_div_log, le_div_iff₀ hl2pos]
    nlinarith
  have hb : Real.logb 2 (2 / δ) ≤ ε * m / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1; linarith
  have hδle : -Real.log δ ≤ Real.log (2 / δ) := by
    rw [Real.log_div (by norm_num) hδ.ne']
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc Real.exp (-(ε * m)) ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by nlinarith)
    _ = δ := Real.exp_log hδ

lemma eight_div_le_of_bound {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {m : ℕ}
    (h2 : 8 * d / ε * Real.logb 2 (13 / ε) ≤ m) : 8 / ε ≤ m := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL13 := one_le_logb_thirteen hε hε1
  calc 8 / ε ≤ 8 * d / ε := by gcongr; linarith
    _ ≤ 8 * d / ε * Real.logb 2 (13 / ε) := le_mul_of_one_le_right (by positivity) hL13
    _ ≤ m := h2

end Numerics

section Main

variable {X : Type*} [MeasurableSpace X]

/-- Parts (2) and (3) for an arbitrary target. -/
lemma consistent_learner_bound (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h) (d : ℕ)
    (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c) (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) (m : ℕ) :
    4 / ε * Real.logb 2 (2 / δ) ≤ m → 8 * d / ε * Real.logb 2 (13 / ε) ≤ m →
      ∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
        (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
        sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal δ := by
  intro h1 h2 L hLH hLc
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hH0 := vcDim_zero_subsingleton H hd
    exact (learner_failure_le_bad H c hc D ε m L hLH hLc).trans
      ((badSample_le_of_subsingleton H hH0 c hc hHm D ε m).trans
        (ENNReal.ofReal_le_ofReal (numeric_bound_zero hε hδ hδ1 h1)))
  · have hm := eight_div_le_of_bound hdpos hε hε1 h2
    exact (learner_failure_le_bad H c hc D ε m L hLH hLc).trans
      ((badSample_le_bound H hHm d hd c hc hwb D hε m hm).trans
        (ENNReal.ofReal_le_ofReal (numeric_bound hdpos hε hε1 hδ h1 h2)))

lemma pacLearnable_of_subset (H : Set (X → Bool)) (hHm : ∀ h ∈ H, Measurable h) (d : ℕ)
    (hd : vcDim H ≤ d) (hne : H.Nonempty) (C : Set (X → Bool)) (hCH : C ⊆ H)
    (hwb : ∀ c' ∈ C, IsWellBehaved H c') : PACLearnable C H := by
  classical
  intro ε δ hε hε2 hδ hδ2
  obtain ⟨m, hm⟩ := exists_nat_ge
    (max (4 / ε * Real.logb 2 (2 / δ)) (8 * d / ε * Real.logb 2 (13 / ε)))
  obtain ⟨h0, hh0⟩ := hne
  let L : (Fin m → X × Bool) → X → Bool := fun S ↦
    if hS : ∃ h ∈ H, IsConsistent h S then hS.choose else h0
  have hLH : ∀ S, L S ∈ H := by
    intro S
    simp only [L]
    split_ifs with hS
    · exact hS.choose_spec.1
    · exact hh0
  refine ⟨m, L, hLH, ?_⟩
  intro c hcC hcm D hD
  have hLc : ∀ S, IsLabeledBy c S → IsConsistent (L S) S := by
    intro S hlab
    have hex : ∃ h ∈ H, IsConsistent h S := ⟨c, hCH hcC, fun i ↦ (hlab i).symm⟩
    simp only [L, dif_pos hex]
    exact hex.choose_spec.2
  exact consistent_learner_bound H hHm d hd c hcm (hwb c hcC) D hε (by linarith) hδ
    (by linarith) m ((le_max_left _ _).trans hm) ((le_max_right _ _).trans hm) L hLH hLc

end Main

theorem vc_sample_bound_main {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hHm : ∀ h ∈ H, Measurable h) (d : ℕ) (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c)
    (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) (m : ℕ) (hm : 8 / ε ≤ m) :
    sampleLaw D c m {S | ¬ IsEpsNet H c D ε (samplePoints S)} ≤
      ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤
        ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)))) ∧
    (4 / ε * Real.logb 2 (2 / δ) ≤ m → 8 * d / ε * Real.logb 2 (13 / ε) ≤ m →
      ∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
        (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
        sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal δ) ∧
    (H.Nonempty → ∀ C : Set (X → Bool), C ⊆ H → (∀ c' ∈ C, IsWellBehaved H c') →
      PACLearnable C H) := by
  refine ⟨epsNet_failure_le H hHm d hd c hc hwb D hε m hm, fun L hLH hLc ↦ ?_,
    consistent_learner_bound H hHm d hd c hc hwb D hε hε1 hδ hδ1 m,
    fun hne C hCH hwbC ↦ pacLearnable_of_subset H hHm d hd hne C hCH hwbC⟩
  exact (learner_failure_le_bad H c hc D ε m L hLH hLc).trans
    (badSample_le_bound H hHm d hd c hc hwb D hε m hm)


end ComputationalLearning

open ComputationalLearning MeasureTheory in
theorem solution {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hHm : ∀ h ∈ H, Measurable h) (d : ℕ) (hd : vcDim H ≤ d) (c : X → Bool) (hc : Measurable c)
    (hwb : IsWellBehaved H c)
    (D : Measure X) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1) (m : ℕ) (hm : 8 / ε ≤ m) :
    sampleLaw D c m {S | ¬ IsEpsNet H c D ε (samplePoints S)} ≤
      ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2))) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤
        ENNReal.ofReal (2 * Phi d (2 * m) * (2 : ℝ) ^ (-(ε * m / 2)))) ∧
    (4 / ε * Real.logb 2 (2 / δ) ≤ m → 8 * d / ε * Real.logb 2 (13 / ε) ≤ m →
      ∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
        (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
        sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal δ) ∧
    (H.Nonempty → ∀ C : Set (X → Bool), C ⊆ H → (∀ c' ∈ C, IsWellBehaved H c') →
      PACLearnable C H) :=
  vc_sample_bound_main H hHm d hd c hc hwb D hε hε1 hδ hδ1 m hm
