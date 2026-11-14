-- Prove2me | solution 1 for BosonicLearn.fockPOVM_compose
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:29:19.429765+00:00
-- url     : https://prove2.me/submissions/1c6e6f26-0960-4c2c-a4b4-2eeb1889c78c

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_effect_matrix_operator
import Theorems.Thm_BosonicLearn_born_truncation
import Theorems.Thm_BosonicLearn_fockPOVM_of_effect
import Theorems.Thm_BosonicLearn_effect_entry_born
import Theorems.Thm_BosonicLearn_kronecker_integral_posSemidef
import Theorems.Thm_BosonicLearn_fockPOVM_postprocess
import Theorems.Thm_BosonicLearn_isDensity_prod

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.RealRegisters (Hilbert)
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix ComplexOrder
open Filter Topology

open BosonicLearn

noncomputable section

/-- The hypothesis `effect_form` of a `FockPOVM`. -/
private abbrev EffB {I : Type} (E : Matrix I I ℂ) : Prop :=
  ∀ (s : Finset I) (z : I → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ∧
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2

/-! ### Entries of effects from Born probabilities -/

private def tS {I : Type} [DecidableEq I] (a b : I) : Fin 4 → Matrix I I ℂ :=
  Classical.choose (effect_entry_born a b)

private def cS {I : Type} [DecidableEq I] (a b : I) : Fin 4 → ℂ :=
  Classical.choose (Classical.choose_spec (effect_entry_born a b))

private lemma tS_density {I : Type} [DecidableEq I] (a b : I) (c : Fin 4) : IsDensity (tS a b c) :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).1 c

private lemma cS_sum {I : Type} [DecidableEq I] (a b : I) :
    ∑ c, cS a b c = (1 : Matrix I I ℂ) a b :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).2.1

private lemma entry_eq {I O : Type} [DecidableEq I] [MeasurableSpace O] (P : FockPOVM I O) {B : Set O}
    (hB : MeasurableSet B) (a b : I) :
    P.effect B a b = ∑ c, cS a b c * (((P.law (tS a b c) B).toReal : ℝ) : ℂ) :=
  (Classical.choose_spec (Classical.choose_spec (effect_entry_born a b))).2.2 O P B hB

/-! ### Bounds and symmetry of effect matrices -/

private lemma norm_entry_le {I : Type} [DecidableEq I] {E : Matrix I I ℂ} (hE : EffB E) (i j : I) :
    ‖E i j‖ ≤ 1 := by
  obtain ⟨F, hF1, -, -, hF4⟩ := effect_matrix_operator E hE
  have h1 : ‖(lp.single 2 i (1 : ℂ) : Hilbert I)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  have h2 : ‖(lp.single 2 j (1 : ℂ) : Hilbert I)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]
    simp
  have h3 : ‖F (lp.single 2 j (1 : ℂ))‖ ≤ 1 := by
    have h := F.le_opNorm (lp.single 2 j (1 : ℂ))
    rw [h2, mul_one] at h
    exact h.trans hF1
  rw [← hF4 i j]
  have h := norm_inner_le_norm (𝕜 := ℂ) (lp.single 2 i (1 : ℂ) : Hilbert I) (F (lp.single 2 j (1 : ℂ)))
  rw [h1, one_mul] at h
  exact h.trans h3

private lemma herm_of_form {I : Type} {E : Matrix I I ℂ}
    (h : ∀ (s : Finset I) (z : I → ℂ), (∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j).im = 0)
    (i j : I) : E j i = star (E i j) := by
  classical
  have hd : ∀ k, (E k k).im = 0 := fun k => by simpa using h {k} (Pi.single k 1)
  by_cases hij : i = j
  · subst hij
    exact (Complex.conj_eq_iff_im.mpr (hd i)).symm
  · have hji : j ≠ i := fun h => hij h.symm
    have hii := hd i
    have hjj := hd j
    have h1 := h {i, j} (fun k => if k = i then 1 else if k = j then 1 else 0)
    have h2 := h {i, j} (fun k => if k = i then 1 else if k = j then Complex.I else 0)
    simp [Finset.sum_pair hij, hji] at h1 h2
    apply Complex.ext
    · simp
      linarith
    · simp
      linarith

/-- The block of an effect matrix on a finite set is positive semidefinite. -/
private lemma eff_block_psd {I : Type} {E : Matrix I I ℂ} (hE : EffB E) (s : Finset I) :
    (Matrix.of fun a b : s => E a b).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact (herm_of_form (fun s z => (hE s z).1) b a).symm
  · let z : I → ℂ := fun i => if h : i ∈ s then x ⟨i, h⟩ else 0
    have h := hE s z
    have e : star x ⬝ᵥ (Matrix.of fun a b : s => E a b).mulVec x =
        ∑ i ∈ s, ∑ j ∈ s, star (z i) * E i j * z j := by
      rw [← Finset.sum_coe_sort s]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [z, mul_assoc]
    rw [e, Complex.nonneg_iff]
    exact ⟨h.2.1, h.1.symm⟩

/-! ### Sections of a measurable set under a Markov kernel -/

private lemma integrable_kernel_sec {Ω O : Type} [MeasurableSpace Ω] [MeasurableSpace O]
    (m : Measure Ω) [IsFiniteMeasure m] (k : Kernel Ω O) [IsMarkovKernel k] {C : Set (Ω × O)}
    (hC : MeasurableSet C) :
    Integrable (fun x => (((k x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ)) m := by
  refine Integrable.of_bound (Complex.measurable_ofReal.comp
    (Kernel.measurable_kernel_prodMk_left hC).ennreal_toReal).aestronglyMeasurable 1
    (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := k x) (s := Prod.mk x ⁻¹' C))

private lemma compProd_toReal {Ω O : Type} [MeasurableSpace Ω] [MeasurableSpace O]
    (m : Measure Ω) [IsFiniteMeasure m] (k : Kernel Ω O) [IsMarkovKernel k] {C : Set (Ω × O)}
    (hC : MeasurableSet C) :
    ((m ⊗ₘ k) C).toReal = ∫ x, (k x (Prod.mk x ⁻¹' C)).toReal ∂m := by
  rw [Measure.compProd_apply hC, integral_toReal
    (Kernel.measurable_kernel_prodMk_left hC).aemeasurable
    (Eventually.of_forall fun x => measure_lt_top _ _)]

section Compose

variable {J I' Ω O : Type} [DecidableEq J] [DecidableEq I'] [MeasurableSpace Ω] [MeasurableSpace O]

/-- The entry `(a, b)` of the effect of `Q_x` on the section `C_x`, as a function of `x`. -/
private def gE (Q : Ω → FockPOVM I' O) (C : Set (Ω × O)) (a b : I') (x : Ω) : ℂ :=
  (Q x).effect (Prod.mk x ⁻¹' C) a b

private lemma gE_eq (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (a b : I') (x : Ω) :
    gE Q C a b x = ∑ d, cS a b d * (((κ (tS a b d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) := by
  unfold gE
  rw [entry_eq (Q x) (measurable_prodMk_left hC) a b]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hκQ _ (tS_density a b d) x]

private lemma gE_measurable (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (a b : I') : Measurable (gE Q C a b) := by
  have h : gE Q C a b =
      fun x => ∑ d, cS a b d * (((κ (tS a b d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) :=
    funext fun x => gE_eq Q κ hκQ hC a b x
  rw [h]
  refine Finset.measurable_sum _ fun d _ => ?_
  have := hκ (tS a b d)
  exact measurable_const.mul
    (Complex.measurable_ofReal.comp (Kernel.measurable_kernel_prodMk_left hC).ennreal_toReal)

private lemma gE_norm_le (Q : Ω → FockPOVM I' O) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (a b : I') (x : Ω) : ‖gE Q C a b x‖ ≤ 1 :=
  norm_entry_le ((Q x).effect_form _ (measurable_prodMk_left hC)) a b

private lemma gE_integrable (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (a b : I') (m : Measure Ω) [IsFiniteMeasure m] :
    Integrable (gE Q C a b) m :=
  Integrable.of_bound (gE_measurable Q κ hκ hκQ hC a b).aestronglyMeasurable 1
    (Eventually.of_forall fun x => gE_norm_le Q hC a b x)

/-- The effect of the composed measurement. -/
private def cEff (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O) (C : Set (Ω × O)) :
    Matrix (J × I') (J × I') ℂ :=
  fun p q => ∑ c, ∑ d, cS p.1 q.1 c * cS p.2 q.2 d *
    ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) C).toReal : ℝ) : ℂ)

/-- `E'(C)_{(u,a),(v,b)} = ∫ Q_x(C_x)_{ab} dM_{uv}(x)`. -/
private lemma cEff_eq (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) (p q : J × I') :
    cEff M κ C p q = ∑ c, cS p.1 q.1 c * ∫ x, gE Q C p.2 q.2 x ∂(M.law (tS p.1 q.1 c)) := by
  unfold cEff
  refine Finset.sum_congr rfl fun c _ => ?_
  have hprob := M.law_prob _ (tS_density p.1 q.1 c)
  have hint : ∫ x, gE Q C p.2 q.2 x ∂(M.law (tS p.1 q.1 c)) =
      ∑ d, cS p.2 q.2 d *
        ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) C).toReal : ℝ) : ℂ) := by
    have h : gE Q C p.2 q.2 = fun x => ∑ d, cS p.2 q.2 d *
        (((κ (tS p.2 q.2 d) x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) :=
      funext fun x => gE_eq Q κ hκQ hC _ _ x
    rw [h, integral_finsetSum _ fun d _ => by
      have := hκ (tS p.2 q.2 d)
      exact (integrable_kernel_sec _ _ hC).const_mul _]
    refine Finset.sum_congr rfl fun d _ => ?_
    have := hκ (tS p.2 q.2 d)
    rw [integral_const_mul, integral_complex_ofReal, compProd_toReal _ _ hC]
  rw [hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

private lemma cEff_univ (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) : cEff M κ Set.univ = 1 := by
  ext p q
  unfold cEff
  have h : ∀ c d, ((((M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d)) Set.univ).toReal : ℝ) : ℂ) = 1 := by
    intro c d
    have := M.law_prob _ (tS_density p.1 q.1 c)
    have := hκ (tS p.2 q.2 d)
    rw [measure_univ]
    simp
  simp only [h, mul_one]
  rw [← Finset.sum_mul_sum, cS_sum, cS_sum]
  simp only [Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [Prod.ext_iff, h1, h2]

private lemma cEff_add_compl (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) {C : Set (Ω × O)} (hC : MeasurableSet C) (p q : J × I') :
    cEff M κ C p q + cEff M κ Cᶜ p q = cEff M κ Set.univ p q := by
  unfold cEff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := M.law_prob _ (tS_density p.1 q.1 c)
  have := hκ (tS p.2 q.2 d)
  rw [← mul_add, ← Complex.ofReal_add, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    measure_add_measure_compl hC]

private lemma cEff_hasSum (M : FockPOVM J Ω) (κ : Matrix I' I' ℂ → Kernel Ω O)
    (hκ : ∀ τ, IsMarkovKernel (κ τ)) (p q : J × I') (f : ℕ → Set (Ω × O))
    (hf : ∀ n, MeasurableSet (f n)) (hd : Pairwise (Function.onFun Disjoint f)) :
    HasSum (fun n => cEff M κ (f n) p q) (cEff M κ (⋃ n, f n) p q) := by
  unfold cEff
  refine hasSum_sum fun c _ => hasSum_sum fun d _ => HasSum.mul_left _ ?_
  have := M.law_prob _ (tS_density p.1 q.1 c)
  have := hκ (tS p.2 q.2 d)
  set ν : Measure (Ω × O) := M.law (tS p.1 q.1 c) ⊗ₘ κ (tS p.2 q.2 d) with hν
  have h1 : ν (⋃ n, f n) = ∑' n, ν (f n) := measure_iUnion hd hf
  have hne : ∑' n, ν (f n) ≠ ⊤ := h1 ▸ measure_ne_top _ _
  have h2 := ENNReal.hasSum_toReal hne
  rw [← ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _), ← h1] at h2
  exact Complex.ofRealCLM.hasSum h2

/-! ### Positivity on entangled vectors -/

private lemma cEff_form_nonneg (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C)
    (s₁ : Finset J) (s₂ : Finset I') (z : J × I' → ℂ) :
    0 ≤ ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * cEff M κ C p q * z q := by
  have hK := kronecker_integral_posSemidef (Ω := Ω) (ι₁ := s₁) (ι₂ := s₂) (K := Fin 4)
    (fun u v c => M.law (tS (u : J) (v : J) c))
    (fun u v c => by
      have := M.law_prob _ (tS_density (u : J) (v : J) c)
      infer_instance)
    (fun u v c => cS (u : J) (v : J) c)
    (fun B hB => by
      have h : (Matrix.of fun u v : s₁ => ∑ c, cS (u : J) (v : J) c *
          (((M.law (tS (u : J) (v : J) c) B).toReal : ℝ) : ℂ)) =
          Matrix.of fun u v : s₁ => M.effect B u v := by
        ext u v
        simp only [Matrix.of_apply]
        exact (entry_eq M hB u v).symm
      rw [h]
      exact eff_block_psd (M.effect_form B hB) s₁)
    (fun x => Matrix.of fun a b : s₂ => gE Q C a b x)
    (fun a b => gE_measurable Q κ hκ hκQ hC a b)
    (fun x a b => gE_norm_le Q hC a b x)
    (fun x => eff_block_psd ((Q x).effect_form _ (measurable_prodMk_left hC)) s₂)
  have h := hK.dotProduct_mulVec_nonneg (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I')))
  have e : star (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I'))) ⬝ᵥ
      (Matrix.of fun (p q : s₁ × s₂) => ∑ k, cS (p.1 : J) (q.1 : J) k *
        ∫ x, (Matrix.of fun a b : s₂ => gE Q C a b x) p.2 q.2
          ∂(M.law (tS (p.1 : J) (q.1 : J) k))).mulVec
        (fun p : s₁ × s₂ => z ((p.1 : J), (p.2 : I'))) =
      ∑ p ∈ s₁ ×ˢ s₂, ∑ q ∈ s₁ ×ˢ s₂, star (z p) * cEff M κ C p q * z q := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Fintype.sum_prod_type,
      Matrix.of_apply, Finset.sum_product]
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_coe_sort s₁]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_coe_sort s₂]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [cEff_eq M Q κ hκ hκQ hC]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rwa [e] at h

private lemma cEff_effB (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {C : Set (Ω × O)} (hC : MeasurableSet C) :
    EffB (cEff M κ C) := by
  have hnn : ∀ {C : Set (Ω × O)}, MeasurableSet C → ∀ (s : Finset (J × I')) (z : J × I' → ℂ),
      0 ≤ ∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q := by
    intro C hC s z
    have h := cEff_form_nonneg M Q κ hκ hκQ hC (s.image Prod.fst) (s.image Prod.snd)
      (fun p => if p ∈ s then z p else 0)
    have hsub : s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have e : ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
        ∑ q ∈ s.image Prod.fst ×ˢ s.image Prod.snd,
          star ((fun p => if p ∈ s then z p else 0) p) * cEff M κ C p q *
            (fun p => if p ∈ s then z p else 0) q =
        ∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q := by
      rw [← Finset.sum_subset hsub (fun p _ hp => by simp [hp])]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_subset hsub (fun q _ hq => by simp [hq])]
      exact Finset.sum_congr rfl fun q hq => by simp [hp, hq]
    rwa [e] at h
  intro s z
  have h1 := hnn hC s z
  have h2 := hnn hC.compl s z
  have hsum : (∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ C p q * z q) +
      (∑ p ∈ s, ∑ q ∈ s, star (z p) * cEff M κ Cᶜ p q * z q) =
      ((∑ p ∈ s, ‖z p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.sum_add_distrib]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_add_distrib]
    have hq : ∀ q ∈ s, star (z p) * cEff M κ C p q * z q + star (z p) * cEff M κ Cᶜ p q * z q =
        star (z p) * (if p = q then 1 else 0) * z q := by
      intro q _
      rw [← add_mul, ← mul_add, cEff_add_compl M κ hκ hC, cEff_univ M κ hκ, Matrix.one_apply]
    rw [Finset.sum_congr rfl hq,
      Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (fun h => absurd hp h),
      if_pos rfl, mul_one, Complex.star_def, Complex.conj_mul']
  rw [Complex.nonneg_iff] at h1 h2
  have hre := congrArg Complex.re hsum
  have him := congrArg Complex.im hsum
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  exact ⟨h1.2.symm, h1.1, by linarith [h2.1]⟩

/-! ### The Born law on product states -/

/-- The Born sum of the composed effect on `ρ ⊗ τ` equals the Born sum on `ρ` of the measurement `M`
post-processed by `x ↦ δ_x ⊗ κ_τ(x)`. -/
private lemma born_prod_eq (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) {ρ : Matrix J J ℂ} {τ : Matrix I' I' ℂ}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) (P' : FockPOVM J (Ω × O))
    (hP' : ∀ σ : Matrix J J ℂ, IsDensity σ → P'.law σ = M.law σ ⊗ₘ κ τ)
    {C : Set (Ω × O)} (hC : MeasurableSet C) :
    (∑' p : J × I', ∑' q : J × I', cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2)) =
      ∑' u, ∑' v, P'.effect C u v * ρ v u := by
  have hX : IsDensity (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) := isDensity_prod hρ hτ
  have hκτ := hκ τ
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  obtain ⟨hX1, -, -⟩ := born_truncation _ hX
  obtain ⟨hρ1, -, -⟩ := born_truncation ρ hρ
  obtain ⟨hτ1, -, hτ3⟩ := born_truncation τ hτ
  obtain ⟨F0, hF0⟩ := hX1 (ε / 3) (by positivity)
  obtain ⟨F10, hF10⟩ := hρ1 (ε / 3) (by positivity)
  set F₁ : Finset J := F10 ∪ F0.image Prod.fst with hF₁def
  set Kρ : ℝ := ∑ u ∈ F₁, ∑ v ∈ F₁, ‖ρ v u‖ * ∑ c, ‖cS u v c‖ with hKdef
  have hKρ : 0 ≤ Kρ := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
    mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun c _ => norm_nonneg _)
  set η : ℝ := ε / 3 / (Kρ + 1) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨F20, hF20⟩ := hτ1 η hη
  set F₂ : Finset I' := F20 ∪ F0.image Prod.snd with hF₂def
  have hsub : F0 ⊆ F₁ ×ˢ F₂ := fun p hp => Finset.mem_product.mpr
    ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  -- the three approximations
  have ha := hF0 (F₁ ×ˢ F₂) hsub (cEff M κ C) (cEff_effB M Q κ hκ hκQ hC)
  have hb := hF10 F₁ Finset.subset_union_left (P'.effect C) (P'.effect_form C hC)
  -- the functions of `x`
  set g₂ : Ω → ℂ := fun x => ∑ a ∈ F₂, ∑ b ∈ F₂, gE Q C a b x * τ b a with hg₂
  set gτ : Ω → ℂ := fun x => (((κ τ x (Prod.mk x ⁻¹' C)).toReal : ℝ) : ℂ) with hgτ
  have hpt : ∀ x, ‖g₂ x - gτ x‖ ≤ η := by
    intro x
    have hEx := (Q x).effect_form _ (measurable_prodMk_left (x := x) hC)
    have h1 := hF20 F₂ Finset.subset_union_left _ hEx
    have h3 := hτ3 _ hEx
    have hlaw := (Q x).law_born τ hτ _ (measurable_prodMk_left (x := x) hC)
    have hval : gτ x = ∑' a, ∑' b, (Q x).effect (Prod.mk x ⁻¹' C) a b * τ b a := by
      simp only [hgτ]
      rw [hκQ τ hτ x, hlaw, ENNReal.toReal_ofReal h3.2]
      exact Complex.ext (by simp) (by simp [h3.1])
    rw [hval, norm_sub_rev]
    exact h1
  have hg₂int : ∀ (m : Measure Ω) [IsFiniteMeasure m], Integrable g₂ m := fun m _ =>
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (gE_integrable Q κ hκ hκQ hC a b m).mul_const _
  have hD : ∀ u v : J, ‖(∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) - P'.effect C u v‖ ≤
      (∑ c, ‖cS u v c‖) * η := by
    intro u v
    have hprob : ∀ c, IsProbabilityMeasure (M.law (tS u v c)) := fun c =>
      M.law_prob _ (tS_density u v c)
    have h1 : ∀ c, ∫ x, g₂ x ∂(M.law (tS u v c)) =
        ∑ a ∈ F₂, ∑ b ∈ F₂, (∫ x, gE Q C a b x ∂(M.law (tS u v c))) * τ b a := by
      intro c
      simp only [hg₂]
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (gE_integrable Q κ hκ hκQ hC a b _).mul_const _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => (gE_integrable Q κ hκ hκQ hC a b _).mul_const _]
      exact Finset.sum_congr rfl fun b _ => integral_mul_const _ _
    have h2 : ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a =
        ∑ c, cS u v c * ∫ x, g₂ x ∂(M.law (tS u v c)) := by
      simp only [h1, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ) (t := F₂)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm (s := Finset.univ) (t := F₂)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [cEff_eq M Q κ hκ hκQ hC, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    have h3 : P'.effect C u v = ∑ c, cS u v c * ∫ x, gτ x ∂(M.law (tS u v c)) := by
      rw [entry_eq P' hC u v]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hP' _ (tS_density u v c), compProd_toReal _ _ hC]
      simp only [hgτ]
      rw [integral_complex_ofReal]
    rw [h2, h3, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← mul_sub, norm_mul, ← integral_sub (hg₂int _) (integrable_kernel_sec _ _ hC)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := norm_integral_le_of_norm_le_const (μ := M.law (tS u v c))
      (Eventually.of_forall fun x => hpt x)
    simpa using h
  -- the truncated sum on the product block
  have hS12 : ∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) =
      ∑ u ∈ F₁, ∑ v ∈ F₁, ρ v u * ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hc : ‖(∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2)) -
      ∑ u ∈ F₁, ∑ v ∈ F₁, P'.effect C u v * ρ v u‖ ≤ ε / 3 := by
    rw [hS12, ← Finset.sum_sub_distrib]
    have hterm : ∀ u ∈ F₁, ‖(∑ v ∈ F₁, ρ v u * ∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) -
        ∑ v ∈ F₁, P'.effect C u v * ρ v u‖ ≤ ∑ v ∈ F₁, ‖ρ v u‖ * (∑ c, ‖cS u v c‖) * η := by
      intro u _
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
      have e : ρ v u * (∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) -
          P'.effect C u v * ρ v u =
          ρ v u * ((∑ a ∈ F₂, ∑ b ∈ F₂, cEff M κ C (u, a) (v, b) * τ b a) - P'.effect C u v) := by
        ring
      rw [e, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hD u v) (norm_nonneg _)
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    have hK : ∑ u ∈ F₁, ∑ v ∈ F₁, ‖ρ v u‖ * (∑ c, ‖cS u v c‖) * η = Kρ * η := by
      rw [hKdef, Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    rw [hK, hηdef]
    have h1 : Kρ * (ε / 3 / (Kρ + 1)) = ε / 3 * (Kρ / (Kρ + 1)) := by ring
    have h2 : Kρ / (Kρ + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    rw [h1]
    calc ε / 3 * (Kρ / (Kρ + 1)) ≤ ε / 3 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ε / 3 := mul_one _
  -- conclusion
  set T : ℂ := ∑' p : J × I', ∑' q : J × I', cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) with hT
  set T' : ℂ := ∑' u, ∑' v, P'.effect C u v * ρ v u with hT'
  set S12 : ℂ := ∑ p ∈ F₁ ×ˢ F₂, ∑ q ∈ F₁ ×ˢ F₂, cEff M κ C p q * (ρ q.1 p.1 * τ q.2 p.2) with hS12def
  set S1 : ℂ := ∑ u ∈ F₁, ∑ v ∈ F₁, P'.effect C u v * ρ v u with hS1def
  have ha' : ‖T - S12‖ ≤ ε / 3 := ha
  have hb' : ‖T' - S1‖ ≤ ε / 3 := hb
  have hsplit : T - T' = (T - S12) + (S12 - S1) - (T' - S1) := by ring
  rw [hsplit]
  calc ‖(T - S12) + (S12 - S1) - (T' - S1)‖ ≤ ‖(T - S12) + (S12 - S1)‖ + ‖T' - S1‖ := norm_sub_le _ _
    _ ≤ ‖T - S12‖ + ‖S12 - S1‖ + ‖T' - S1‖ := by linarith [norm_add_le (T - S12) (S12 - S1)]
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

end Compose

/-! ### The statement -/

theorem solution {J I' Ω O : Type} [DecidableEq J] [DecidableEq I'] [MeasurableSpace Ω]
    [MeasurableSpace O] (M : FockPOVM J Ω) (Q : Ω → FockPOVM I' O)
    (κ : Matrix I' I' ℂ → Kernel Ω O) (hκ : ∀ τ, IsMarkovKernel (κ τ))
    (hκQ : ∀ τ, IsDensity τ → ∀ x, κ τ x = (Q x).law τ) :
    ∃ M' : FockPOVM (J × I') (Ω × O), ∀ (ρ : Matrix J J ℂ) (τ : Matrix I' I' ℂ),
      IsDensity ρ → IsDensity τ →
        M'.law (fun p q => ρ p.1 q.1 * τ p.2 q.2) = (M.law ρ) ⊗ₘ (κ τ) := by
  obtain ⟨M', hM'⟩ := fockPOVM_of_effect (cEff M κ) (fun C hC => cEff_effB M Q κ hκ hκQ hC)
    (cEff_univ M κ hκ) (fun p q f hf hd => cEff_hasSum M κ hκ p q f hf hd)
  refine ⟨M', fun ρ τ hρ hτ => ?_⟩
  have hX : IsDensity (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) := isDensity_prod hρ hτ
  have hκτ := hκ τ
  obtain ⟨P', hP'⟩ := fockPOVM_postprocess M (Kernel.id ×ₖ κ τ) inferInstance
  have hP'law : ∀ σ : Matrix J J ℂ, IsDensity σ → P'.law σ = M.law σ ⊗ₘ κ τ := by
    intro σ hσ
    have := M.law_prob σ hσ
    rw [hP' σ, Measure.compProd_eq_comp_prod]
  refine Measure.ext fun C hC => ?_
  have key := born_prod_eq M Q κ hκ hκQ hρ hτ P' hP'law hC
  have key' : (∑' i, ∑' j, cEff M κ C i j * (fun p q : J × I' => ρ p.1 q.1 * τ p.2 q.2) j i) =
      ∑' u, ∑' v, P'.effect C u v * ρ v u := key
  rw [M'.law_born _ hX C hC, hM', key', ← hP'law ρ hρ, P'.law_born ρ hρ C hC]
