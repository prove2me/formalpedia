-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.step_d_kl_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:56:32.455366+00:00
-- url     : https://prove2.me/submissions/a44dfe33-35fd-416c-96e1-c97ca0db7e86

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction
import Theorems.Thm_FirstPriceLearning_ContextLowerBound_property_5

open MeasureTheory InformationTheory ProbabilityTheory

namespace CLBKL

variable {H Y A : Type} [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace A]
  [Countable A] [MeasurableSingletonClass A]

/-- The kernel `h ↦ ν (a h)`. -/
noncomputable def kerOf (ν : A → Measure Y) (a : H → A) (ha : Measurable a) : Kernel H Y :=
  Kernel.comap (Kernel.ofFunOfCountable ν) a ha

lemma kerOf_apply (ν : A → Measure Y) (a : H → A) (ha : Measurable a) (h : H) :
    kerOf ν a ha h = ν (a h) := rfl

instance kerOf_markov (ν : A → Measure Y) [∀ b, IsProbabilityMeasure (ν b)] (a : H → A)
    (ha : Measurable a) : IsMarkovKernel (kerOf ν a ha) :=
  ⟨fun h => by rw [kerOf_apply]; infer_instance⟩

/-- Conditional KL for kernels factoring through a countable variable. -/
theorem klDiv_compProd_kerOf (μ : Measure H) [IsFiniteMeasure μ] (ν' ν : A → Measure Y)
    [∀ b, IsProbabilityMeasure (ν' b)] [∀ b, IsProbabilityMeasure (ν b)]
    (hac : ∀ b, ν' b ≪ ν b) (a : H → A) (ha : Measurable a) :
    klDiv (μ ⊗ₘ kerOf ν' a ha) (μ ⊗ₘ kerOf ν a ha) = ∫⁻ h, klDiv (ν' (a h)) (ν (a h)) ∂μ := by
  set f : H → Y → ENNReal := fun h y => (ν' (a h)).rnDeriv (ν (a h)) y with hf
  have hg : Measurable (Function.uncurry fun (b : A) (y : Y) => (ν' b).rnDeriv (ν b) y) := by
    apply measurable_from_prod_countable_right
    intro b
    change Measurable fun y => (ν' b).rnDeriv (ν b) y
    exact Measure.measurable_rnDeriv _ _
  have hfm : Measurable (Function.uncurry f) :=
    hg.comp ((ha.comp measurable_fst).prodMk measurable_snd)
  have hker : kerOf ν' a ha = (kerOf ν a ha).withDensity f := by
    ext1 h
    rw [Kernel.withDensity_apply _ hfm, kerOf_apply, kerOf_apply]
    exact (Measure.withDensity_rnDeriv_eq _ _ (hac (a h))).symm
  have : IsSFiniteKernel ((kerOf ν a ha).withDensity f) := by
    rw [← hker]; infer_instance
  have hcp : μ ⊗ₘ kerOf ν' a ha = (μ ⊗ₘ kerOf ν a ha).withDensity (fun p => f p.1 p.2) := by
    rw [hker]; exact Measure.compProd_withDensity hfm
  have hac2 : μ ⊗ₘ kerOf ν' a ha ≪ μ ⊗ₘ kerOf ν a ha := by
    rw [hcp]; exact withDensity_absolutelyContinuous _ _
  rw [klDiv_eq_lintegral_klFun_of_ac hac2]
  have hrn : (μ ⊗ₘ kerOf ν' a ha).rnDeriv (μ ⊗ₘ kerOf ν a ha) =ᵐ[μ ⊗ₘ kerOf ν a ha]
      (fun p => f p.1 p.2) := by
    rw [hcp]; exact Measure.rnDeriv_withDensity _ hfm
  have hF : Measurable (fun p : H × Y => ENNReal.ofReal (klFun (f p.1 p.2).toReal)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_klFun.comp (ENNReal.measurable_toReal.comp hfm))
  rw [lintegral_congr_ae (g := fun p => ENNReal.ofReal (klFun (f p.1 p.2).toReal))
    (hrn.mono (fun p hp => by rw [hp]))]
  rw [Measure.lintegral_compProd hF]
  apply lintegral_congr
  intro h
  rw [kerOf_apply, klDiv_eq_lintegral_klFun_of_ac (hac (a h))]

end CLBKL

namespace CLBD

open FirstPriceLearning.ContextLowerBound

variable {M : ℕ} {A U : Type} [MeasurableSpace A] [MeasurableSpace U]

abbrev X (M : ℕ) (A : Type) := Fin M → A → ℝ

/-- Observations up to round `t` depend only on the rewards of rounds `< t`. -/
lemma obs_congr (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M) (u : U)
    (r r' : Fin T → Fin M → A → ℝ) :
    ∀ (t : ℕ) (h : t ≤ T), (∀ j : Fin T, j.val < t → r j = r' j) →
      observations E π c u r t h = observations E π c u r' t h := by
  intro t
  induction t with
  | zero => intro h _; funext i; exact i.elim0
  | succ t ih =>
    intro h hr
    have hp := ih (Nat.le_of_succ_le h) (fun j hj => hr j (by omega))
    simp only [observations]
    rw [hp, hr ⟨t, h⟩ (by simp)]


section Indep

variable [Countable A] [MeasurableSingletonClass A]

lemma measurable_reveal_comp {Ω : Type} [MeasurableSpace Ω] (E : A → A → Prop) {a : Ω → A}
    {x : Ω → Fin M → A → ℝ} (ha : Measurable a) (hx : Measurable x) :
    Measurable (fun ω => reveal E (a ω) (x ω)) := by
  classical
  refine measurable_pi_lambda _ (fun c => measurable_pi_lambda _ (fun b => ?_))
  simp only [reveal]
  refine Measurable.ite ?_ ((measurable_pi_apply b).comp ((measurable_pi_apply c).comp hx))
    measurable_const
  exact ha (Set.to_countable {a' : A | FirstPriceLearning.GraphFeedback.Revealed E a' b}).measurableSet

lemma measurable_observations (E : A → A → Prop) (π : Policy M A U) {T : ℕ}
    (c : Fin T → Fin M) :
    ∀ (t : ℕ) (h : t ≤ T),
      Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) => observations E π c ω.1 ω.2 t h) := by
  intro t
  induction t with
  | zero => intro h; exact measurable_pi_lambda _ (fun i => i.elim0)
  | succ t ih =>
    intro h
    have hprev := ih (Nat.le_of_succ_le h)
    have hact : Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) =>
        π.act t ω.1 (fun i => c ⟨i.val, by omega⟩)
          (observations E π c ω.1 ω.2 t (Nat.le_of_succ_le h))) := by
      have := π.measurable_act t
      exact this.comp (measurable_fst.prodMk (measurable_const.prodMk hprev))
    have hnew : Measurable (fun ω : U × (Fin T → Fin M → A → ℝ) =>
        reveal E (π.act t ω.1 (fun i => c ⟨i.val, by omega⟩)
          (observations E π c ω.1 ω.2 t (Nat.le_of_succ_le h))) (ω.2 ⟨t, h⟩)) :=
      measurable_reveal_comp E hact ((measurable_pi_apply _).comp measurable_snd)
    simp only [observations]
    refine measurable_pi_lambda _ (fun i => ?_)
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hnew
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp hprev

/-- The history map `ω ↦ (u, observations of the first t rounds)`. -/
noncomputable def histMap (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (t : ℕ) (ht : t ≤ T) : U × (Fin T → X M A) → U × (Fin t → X M A) :=
  fun ω => (ω.1, observations E π c ω.1 ω.2 t ht)

lemma measurable_histMap (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (t : ℕ) (ht : t ≤ T) : Measurable (histMap E π c t ht) :=
  measurable_fst.prodMk (measurable_observations E π c t ht)

/-- The rewards of round `t` are independent of the history before round `t`. -/
lemma indep_round (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P : Measure (X M A)) [IsProbabilityMeasure P]
    (t : ℕ) (ht : t < T) :
    (μU.prod (Measure.pi fun _ : Fin T => P)).map
        (fun ω => (histMap E π c t ht.le ω, ω.2 ⟨t, ht⟩)) =
      ((μU.prod (Measure.pi fun _ : Fin T => P)).map (histMap E π c t ht.le)).prod P := by
  classical
  set i : Fin T := ⟨t, ht⟩ with hi
  set p : Fin T → Prop := fun j => j ≠ i with hp
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin T => X M A) p with he
  have hpres := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin T => P) p
  set ν1 := Measure.pi fun _ : Subtype p => P with hν1
  set ν2 := Measure.pi fun _ : {j // ¬ p j} => P with hν2
  set i0 : {j // ¬ p j} := ⟨i, by simp [hp]⟩ with hi0
  set F : U × (Subtype p → X M A) → U × (Fin t → X M A) :=
    fun q => histMap E π c t ht.le (q.1, e.symm (q.2, 0)) with hFdef
  have hF : Measurable F := (measurable_histMap E π c t ht.le).comp
    (measurable_fst.prodMk (e.symm.measurable.comp (measurable_snd.prodMk measurable_const)))
  set Ψ : (U × (Subtype p → X M A)) × ({j // ¬ p j} → X M A) → U × (Fin T → X M A) :=
    fun q => (q.1.1, e.symm (q.1.2, q.2)) with hΨdef
  have hΨ : Measurable Ψ := (measurable_fst.comp measurable_fst).prodMk
    (e.symm.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hL : μU.prod (Measure.pi fun _ : Fin T => P) = ((μU.prod ν1).prod ν2).map Ψ := by
    have h1 : Measure.pi (fun _ : Fin T => P) = (ν1.prod ν2).map e.symm := hpres.symm.map_eq.symm
    rw [h1]
    have h2 := Measure.map_prod_map μU (ν1.prod ν2) measurable_id e.symm.measurable
    rw [Measure.map_id] at h2
    rw [h2, ← (measurePreserving_prodAssoc μU ν1 ν2).map_eq,
      Measure.map_map (measurable_id.prodMap e.symm.measurable) MeasurableEquiv.prodAssoc.measurable]
    rfl
  have hloc : ∀ (u : U) (w1 : Subtype p → X M A) (w2 : {j // ¬ p j} → X M A),
      histMap E π c t ht.le (u, e.symm (w1, w2)) = F (u, w1) := by
    intro u w1 w2
    simp only [hFdef, histMap]
    congr 1
    apply obs_congr
    intro j hj
    have hj' : p j := by
      simp only [hp, ne_eq]
      intro h; rw [h] at hj; simp [hi] at hj
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, hj']
  have hev : ∀ (w1 : Subtype p → X M A) (w2 : {j // ¬ p j} → X M A),
      e.symm (w1, w2) i = w2 i0 := by
    intro w1 w2
    have : ¬ p i := by simp [hp]
    simp [he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, this, hi0]
  have hcomp1 : (fun ω => (histMap E π c t ht.le ω, ω.2 i)) ∘ Ψ =
      Prod.map F (fun w => w i0) := by
    funext q
    obtain ⟨⟨u, w1⟩, w2⟩ := q
    simp only [Function.comp, hΨdef, Prod.map]
    rw [hloc, hev]
  have hcomp2 : histMap E π c t ht.le ∘ Ψ = F ∘ Prod.fst := by
    funext q
    obtain ⟨⟨u, w1⟩, w2⟩ := q
    simp only [Function.comp, hΨdef]
    rw [hloc]
  have hm1 : Measurable (fun ω : U × (Fin T → X M A) => (histMap E π c t ht.le ω, ω.2 i)) :=
    (measurable_histMap E π c t ht.le).prodMk ((measurable_pi_apply i).comp measurable_snd)
  rw [hL, Measure.map_map hm1 hΨ, hcomp1, Measure.map_map (measurable_histMap E π c t ht.le) hΨ,
    hcomp2, ← Measure.map_prod_map _ _ hF (measurable_pi_apply i0),
    (measurePreserving_eval (fun _ : {j // ¬ p j} => P) i0).map_eq,
    ← Measure.map_map hF measurable_fst, Measure.map_fst_prod]
  simp

end Indep


section Step

variable [Countable A] [MeasurableSingletonClass A]

/-- A composition product with a kernel of pushforwards is a pushforward of a product. -/
lemma compProd_kerOf_map {H Y Z : Type} [MeasurableSpace H] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure H) [SFinite μ] (P : Measure Y) [IsProbabilityMeasure P]
    (g : A → Y → Z) (hg : Measurable (Function.uncurry g)) (a : H → A) (ha : Measurable a) :
    μ ⊗ₘ CLBKL.kerOf (fun b => P.map (g b)) a ha =
      (μ.prod P).map (fun q => (q.1, g (a q.1) q.2)) := by
  have hgb : ∀ b, Measurable (g b) := fun b => hg.comp (measurable_const.prodMk measurable_id)
  have hV : Measurable (fun q : H × Y => (q.1, g (a q.1) q.2)) :=
    measurable_fst.prodMk (hg.comp ((ha.comp measurable_fst).prodMk measurable_snd))
  have : ∀ b, IsProbabilityMeasure (P.map (g b)) :=
    fun b => Measure.isProbabilityMeasure_map (hgb b).aemeasurable
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hV hs, Measure.prod_apply (hV hs)]
  apply lintegral_congr
  intro h
  rw [CLBKL.kerOf_apply, Measure.map_apply (hgb (a h)) (measurable_prodMk_left hs)]
  rfl

/-- The action at round `t` as a function of the history. -/
noncomputable def actH (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M) (t : ℕ) (ht : t < T) :
    U × (Fin t → X M A) → A :=
  fun h => π.act t h.1 (fun i => c ⟨i.val, by omega⟩) h.2

lemma measurable_actH (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M) (t : ℕ) (ht : t < T) :
    Measurable (actH π c t ht) :=
  (π.measurable_act t).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- Appending the observation of round `t`. -/
def snocMap (t : ℕ) : (U × (Fin t → X M A)) × X M A → U × (Fin (t + 1) → X M A) :=
  fun q => (q.1.1, Fin.snoc q.1.2 q.2)

lemma measurable_snocMap (t : ℕ) : Measurable (snocMap (M := M) (A := A) (U := U) t) := by
  refine (measurable_fst.comp measurable_fst).prodMk ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

lemma measurable_reveal_uncurry (E : A → A → Prop) :
    Measurable (Function.uncurry fun (b : A) (x : X M A) => reveal E b x) :=
  measurable_reveal_comp E measurable_fst measurable_snd

/-- The law of the history at round `t` under reward law `P`. -/
noncomputable def histLaw (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) (P : Measure (X M A)) (t : ℕ) (ht : t ≤ T) :
    Measure (U × (Fin t → X M A)) :=
  (μU.prod (Measure.pi fun _ : Fin T => P)).map (histMap E π c t ht)

instance histLaw_prob (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P : Measure (X M A)) [IsProbabilityMeasure P]
    (t : ℕ) (ht : t ≤ T) : IsProbabilityMeasure (histLaw E π c μU P t ht) :=
  Measure.isProbabilityMeasure_map (measurable_histMap E π c t ht).aemeasurable

/-- One-step recursion of the history law. -/
lemma histLaw_succ (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P : Measure (X M A)) [IsProbabilityMeasure P]
    (t : ℕ) (ht : t < T) :
    histLaw E π c μU P (t + 1) ht =
      Measure.map (snocMap t) (histLaw E π c μU P t ht.le ⊗ₘ
        CLBKL.kerOf (fun b => P.map (reveal E b)) (actH π c t ht) (measurable_actH π c t ht)) := by
  rw [compProd_kerOf_map _ _ _ (measurable_reveal_uncurry E) _ (measurable_actH π c t ht)]
  unfold histLaw
  rw [← indep_round E π c μU P t ht]
  have hm1 : Measurable (fun ω : U × (Fin T → X M A) =>
      (histMap E π c t ht.le ω, ω.2 ⟨t, ht⟩)) :=
    (measurable_histMap E π c t ht.le).prodMk ((measurable_pi_apply _).comp measurable_snd)
  have hV : Measurable (fun q : (U × (Fin t → X M A)) × X M A =>
      (q.1, reveal E (actH π c t ht q.1) q.2)) :=
    measurable_fst.prodMk ((measurable_reveal_uncurry E).comp
      (((measurable_actH π c t ht).comp measurable_fst).prodMk measurable_snd))
  rw [Measure.map_map hV hm1, Measure.map_map (measurable_snocMap t) (hV.comp hm1)]
  rfl

end Step


section KL

variable [Countable A] [MeasurableSingletonClass A]

lemma kl_step (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P' P : Measure (X M A))
    [IsProbabilityMeasure P'] [IsProbabilityMeasure P]
    (hac : ∀ b, P'.map (reveal E b) ≪ P.map (reveal E b)) (t : ℕ) (ht : t < T) :
    klDiv (histLaw E π c μU P' (t + 1) ht) (histLaw E π c μU P (t + 1) ht) ≤
      klDiv (histLaw E π c μU P' t ht.le) (histLaw E π c μU P t ht.le) +
        ∫⁻ h, klDiv (P'.map (reveal E (actH π c t ht h))) (P.map (reveal E (actH π c t ht h)))
          ∂(histLaw E π c μU P' t ht.le) := by
  have h1 : ∀ b, IsProbabilityMeasure (P'.map (reveal E b)) := fun b =>
    Measure.isProbabilityMeasure_map
      ((measurable_reveal_uncurry E).comp (measurable_const.prodMk measurable_id)).aemeasurable
  have h2 : ∀ b, IsProbabilityMeasure (P.map (reveal E b)) := fun b =>
    Measure.isProbabilityMeasure_map
      ((measurable_reveal_uncurry E).comp (measurable_const.prodMk measurable_id)).aemeasurable
  rw [histLaw_succ E π c μU P' t ht, histLaw_succ E π c μU P t ht]
  refine (klDiv_map_le _ _ (measurable_snocMap t)).trans (le_of_eq ?_)
  rw [klDiv_compProd_eq_add, CLBKL.klDiv_compProd_kerOf _ _ _ hac]

lemma lintegral_kl_le (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P' P : Measure (X M A))
    [IsProbabilityMeasure P'] (D : ℝ) (R : Set A)
    (hb : ∀ b, klDiv (P'.map (reveal E b)) (P.map (reveal E b)) ≤
      ENNReal.ofReal (D * R.indicator (fun _ => (1 : ℝ)) b)) (t : ℕ) (ht : t < T) :
    ∫⁻ h, klDiv (P'.map (reveal E (actH π c t ht h))) (P.map (reveal E (actH π c t ht h)))
        ∂(histLaw E π c μU P' t ht.le) ≤
      ENNReal.ofReal D * (μU.prod (Measure.pi fun _ : Fin T => P'))
        {ω | action E π c ω.1 ω.2 ⟨t, ht⟩ ∈ R} := by
  classical
  have hS : MeasurableSet (actH π c t ht ⁻¹' R) :=
    (measurable_actH π c t ht) (Set.to_countable R).measurableSet
  calc _ ≤ ∫⁻ h, (actH π c t ht ⁻¹' R).indicator (fun _ => ENNReal.ofReal D) h
        ∂(histLaw E π c μU P' t ht.le) := by
        apply lintegral_mono
        intro h
        refine (hb _).trans (le_of_eq ?_)
        by_cases hh : actH π c t ht h ∈ R
        · rw [Set.indicator_of_mem (show h ∈ actH π c t ht ⁻¹' R from hh),
            Set.indicator_of_mem hh, mul_one]
        · rw [Set.indicator_of_notMem (show h ∉ actH π c t ht ⁻¹' R from hh),
            Set.indicator_of_notMem hh, mul_zero, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal D * histLaw E π c μU P' t ht.le (actH π c t ht ⁻¹' R) :=
        lintegral_indicator_const hS _
    _ = _ := by
        unfold histLaw
        rw [Measure.map_apply (measurable_histMap E π c t ht.le) hS]
        rfl

lemma histLaw_zero (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P' P : Measure (X M A))
    [IsProbabilityMeasure P'] [IsProbabilityMeasure P] :
    histLaw E π c μU P' 0 (Nat.zero_le T) = histLaw E π c μU P 0 (Nat.zero_le T) := by
  have key : ∀ Q : Measure (X M A), IsProbabilityMeasure Q →
      histLaw E π c μU Q 0 (Nat.zero_le T) =
        μU.map (fun u => (u, (fun i => i.elim0 : Fin 0 → X M A))) := by
    intro Q hQ
    have hg : Measurable (fun u : U => (u, (fun i => i.elim0 : Fin 0 → X M A))) :=
      measurable_id.prodMk measurable_const
    have : histMap E π c 0 (Nat.zero_le T) =
        (fun u : U => (u, (fun i => i.elim0 : Fin 0 → X M A))) ∘ Prod.fst := by
      funext ω
      simp only [histMap, Function.comp]
      congr 1
    unfold histLaw
    rw [this, ← Measure.map_map hg measurable_fst, Measure.map_fst_prod]
    simp
  rw [key P' inferInstance, key P inferInstance]

theorem kl_hist (E : A → A → Prop) (π : Policy M A U) {T : ℕ} (c : Fin T → Fin M)
    (μU : Measure U) [IsProbabilityMeasure μU] (P' P : Measure (X M A))
    [IsProbabilityMeasure P'] [IsProbabilityMeasure P] (D : ℝ) (R : Set A)
    (hb : ∀ b, klDiv (P'.map (reveal E b)) (P.map (reveal E b)) ≤
      ENNReal.ofReal (D * R.indicator (fun _ => (1 : ℝ)) b)) :
    ∀ (t : ℕ) (ht : t ≤ T),
      klDiv (histLaw E π c μU P' t ht) (histLaw E π c μU P t ht) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
          ENNReal.ofReal D * (μU.prod (Measure.pi fun _ : Fin T => P'))
            {ω | action E π c ω.1 ω.2 s ∈ R} := by
  classical
  have hac : ∀ b, P'.map (reveal E b) ≪ P.map (reveal E b) := by
    intro b
    exact (klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb b))).1
  intro t
  induction t with
  | zero =>
    intro ht
    rw [histLaw_zero E π c μU P' P, klDiv_self]
    exact bot_le
  | succ t ih =>
    intro ht
    have ht' : t < T := ht
    refine (kl_step E π c μU P' P hac t ht').trans ?_
    refine (add_le_add (ih ht'.le) (lintegral_kl_le E π c μU P' P D R hb t ht')).trans
      (le_of_eq ?_)
    rw [Finset.sum_filter, Finset.sum_filter]
    rw [show ∑ s : Fin T, (if s.val < t + 1 then ENNReal.ofReal D *
          (μU.prod (Measure.pi fun _ : Fin T => P')) {ω | action E π c ω.1 ω.2 s ∈ R} else 0) =
        ∑ s : Fin T, ((if s.val < t then ENNReal.ofReal D *
          (μU.prod (Measure.pi fun _ : Fin T => P')) {ω | action E π c ω.1 ω.2 s ∈ R} else 0) +
          (if s = ⟨t, ht'⟩ then ENNReal.ofReal D *
          (μU.prod (Measure.pi fun _ : Fin T => P')) {ω | action E π c ω.1 ω.2 s ∈ R} else 0))
        from Finset.sum_congr rfl (fun s _ => by
          by_cases h1 : s.val < t
          · have h2 : s ≠ ⟨t, ht'⟩ := by intro h; rw [h] at h1; simp at h1
            simp [h1, h2, show s.val < t + 1 by omega]
          · by_cases h2 : s = ⟨t, ht'⟩
            · subst h2; simp
            · have h3 : ¬ s.val < t + 1 := by
                intro h; apply h2; apply Fin.ext; simp; omega
              simp [h1, h2, h3])]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp

end KL

end CLBD

open FirstPriceLearning.ContextLowerBound

namespace CLBH

lemma gap_nonneg (M α T : ℕ) : 0 ≤ gap M α T := Real.sqrt_nonneg _

lemma gap_le (M α T : ℕ) (hT : (α + 1) * M ≤ T) : gap M α T ≤ 1 / 4 := by
  unfold gap
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    have : ((((α + 1) * M : ℕ)) : ℝ) ≤ T := by exact_mod_cast hT
    linarith

lemma gap_pos (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T) : 0 < gap M α T := by
  unfold gap
  apply Real.sqrt_pos.mpr
  have hK : 0 < (α + 1) * M := by positivity
  have hTp : 0 < T := lt_of_lt_of_le hK hT
  have h1 : (0 : ℝ) < (((α + 1) * M : ℕ) : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < T := by exact_mod_cast hTp
  positivity

lemma hardMean_bounds (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : 0 ≤ hardMean M α T u c a ∧ hardMean M α T u c a ≤ 1 := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  unfold hardMean
  split_ifs <;> constructor <;> linarith

lemma bern_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (bernoulliReal p) := by
  constructor
  simp only [bernoulliReal, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

lemma integral_bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∫ x, x ∂(bernoulliReal p) = p := by
  unfold bernoulliReal
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [ENNReal.toReal_ofReal h0]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma hardLaw_prob (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsProbabilityMeasure (hardLaw M α T u) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  unfold hardLaw
  infer_instance

lemma map_coord (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) :
    (hardLaw M α T u).map (fun x => x c a) = bernoulliReal (hardMean M α T u c a) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  have h1 := (measurePreserving_eval
    (fun c => Measure.pi fun a => bernoulliReal (hardMean M α T u c a)) c).map_eq
  have h2 := (measurePreserving_eval (fun a => bernoulliReal (hardMean M α T u c a)) a).map_eq
  have : (fun x : Fin M → Act M α → ℝ => x c a) =
      (Function.eval a : (Act M α → ℝ) → ℝ) ∘ (Function.eval c : (Fin M → Act M α → ℝ) → _) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply a) (measurable_pi_apply c)]
  unfold hardLaw
  rw [h1, h2]

lemma meanReward_hard (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : meanReward (hardLaw M α T u) c a = hardMean M α T u c a := by
  unfold meanReward
  have hm : Measurable (fun x : Fin M → Act M α → ℝ => x c a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply c)
  have := integral_map (μ := hardLaw M α T u) hm.aemeasurable
    (aestronglyMeasurable_id (μ := (hardLaw M α T u).map (fun x => x c a)))
  simp only [id] at this
  rw [← this, map_coord M α T hT u c a]
  exact integral_bern _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2

end CLBH

open FirstPriceLearning.ContextLowerBound in
theorem solution (M α T : ℕ) (hT : (α + 1) * M ≤ T)
    {U : Type} [MeasurableSpace U] (μU : Measure U) [IsProbabilityMeasure μU]
    (π : Policy M (Act M α) U) (ctx : Fin T → Fin M) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (hu : u c ≠ 0) (t : ℕ) (ht : t ≤ T) :
    klDiv ((interactionLaw μU (hardLaw M α T (Function.update u c 0)) T).map
          (fun ω => (ω.1, observations (feedbackGraph M α) π ctx ω.1 ω.2 t ht)))
        ((interactionLaw μU (hardLaw M α T u) T).map
          (fun ω => (ω.1, observations (feedbackGraph M α) π ctx ω.1 ω.2 t ht))) ≤
      ENNReal.ofReal (64 / 3 * gap M α T ^ 2 *
        ∑ s ∈ Finset.univ.filter (fun s : Fin T => s.val < t),
          (interactionLaw μU (hardLaw M α T (Function.update u c 0)) T
            {ω | (action (feedbackGraph M α) π ctx ω.1 ω.2 s).1 < c ∨
              action (feedbackGraph M α) π ctx ω.1 ω.2 s = (c, u c)}).toReal) := by
  classical
  set D : ℝ := 64 / 3 * gap M α T ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set R : Set (Act M α) := {b | b.1 < c ∨ b = (c, u c)} with hR
  have h1 := CLBH.hardLaw_prob M α T hT (Function.update u c 0)
  have h2 := CLBH.hardLaw_prob M α T hT u
  have hb : ∀ b, klDiv ((hardLaw M α T (Function.update u c 0)).map (reveal (feedbackGraph M α) b))
      ((hardLaw M α T u).map (reveal (feedbackGraph M α) b)) ≤
      ENNReal.ofReal (D * R.indicator (fun _ => (1 : ℝ)) b) := by
    intro b
    have h5 := (property_5 M α T hT u c hu b).2
    refine h5.trans (le_of_eq ?_)
    congr 2
    by_cases hbR : b.1 < c ∨ b = (c, u c)
    · rw [if_pos hbR, Set.indicator_of_mem (show b ∈ R from hbR)]
    · rw [if_neg hbR, Set.indicator_of_notMem (show b ∉ R from hbR)]
  have key := CLBD.kl_hist (feedbackGraph M α) π ctx μU (hardLaw M α T (Function.update u c 0))
    (hardLaw M α T u) D R hb t ht
  refine key.trans (le_of_eq ?_)
  rw [← Finset.mul_sum, ENNReal.ofReal_mul hD0,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have : IsProbabilityMeasure (interactionLaw μU (hardLaw M α T (Function.update u c 0)) T) := by
    unfold interactionLaw; infer_instance
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl
