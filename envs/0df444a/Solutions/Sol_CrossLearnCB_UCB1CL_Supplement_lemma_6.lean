-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.Supplement.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:35.088301+00:00
-- url     : https://prove2.me/submissions/0cc2fed9-ecb7-4ba3-b18a-2b28aa467b59

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Supplement_RoundRegret

open CrossLearnCB
open CrossLearnCB.UCB1CL
open CrossLearnCB.UCB1CL.Supplement

/-- Lemma 6, p. 51. A finite uniform distribution over stochastic one-context instances
forces Ω(√(K/T)) expected pseudo-regret in every round, for every algorithm. -/
theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) [NeZero K], 2 ≤ K →
    ∃ T₀ : ℕ, 0 < T₀ ∧ ∀ T : ℕ, T₀ ≤ T →
    ∃ m : ℕ, 0 < m ∧ ∃ S : Fin m → StochInstance K 1,
      (∀ j, (S j).IsCoordinateIndependent) ∧ ∀ A : Policy K 1, A.IsValid → A.IsMeasurable → ∀ t : Fin T,
        c * Real.sqrt ((K : ℝ) / T) ≤
          (1 / (m : ℝ)) * ∑ j : Fin m, roundStochRegret t (fun _ _ _ => True) (S j) A := by
            set_option maxHeartbeats 1000000 in
              classical
              have gen : ∀ (β : Type) [Fintype β] [DecidableEq β] [Nonempty β]
                  (n : ℕ) (q : Fin n → (Fin n → β) → ℝ),
                  (∀ s τ τ', (∀ u, u ≤ s → τ u = τ' u) → q s τ = q s τ') →
                  (∀ s τ, ∑ a, q s (Function.update τ s a) = 1) → ∑ τ, ∏ s, q s τ = 1 := by
                intro β _ _ _ n
                induction n with
                | zero => intro q _ _; simp
                | succ n ih =>
                  intro q hdep hsum
                  let d : β := Classical.choice ‹Nonempty β›
                  have hind : ∀ (i : Fin n) (x : Fin n → β) (a : β),
                      q i.castSucc (Fin.snoc x a) = q i.castSucc (Fin.snoc x d) := by
                    intro i x a
                    apply hdep
                    intro u hu
                    cases u using Fin.lastCases with
                    | last => have := i.isLt; change n ≤ i.val at hu; omega
                    | cast u => simp
                  rw [← (Fin.snocEquiv (fun _ => β)).sum_comp, Fintype.sum_prod_type_right]
                  change (∑ x : Fin n → β, ∑ a : β, ∏ s, q s (Fin.snoc x a)) = 1
                  simp only [Fin.prod_univ_castSucc]
                  have hs : ∀ x : Fin n → β, ∑ a, q (Fin.last n) (Fin.snoc x a) = 1 := by
                    intro x
                    simpa only [Fin.update_snoc_last] using hsum (Fin.last n) (Fin.snoc x d)
                  simp_rw [hind]
                  simp_rw [← Finset.mul_sum, hs, mul_one]
                  apply ih
                  · intro i x y hxy
                    apply hdep
                    intro u hu
                    cases u using Fin.lastCases with
                    | last => have := i.isLt; change n ≤ i.val at hu; omega
                    | cast u => simpa using hxy u hu
                  · intro i x
                    simpa only [Fin.snoc_update] using hsum i.castSucc (Fin.snoc x d)
              have push : ∀ (ι α β : Type) [Fintype ι] [Fintype α] [Fintype β]
                  [DecidableEq ι] [DecidableEq β] (w : ι → α → ℝ) (f : ι → α → β) (g : (ι → β) → ℝ),
                  (∑ x : ι → α, (∏ i, w i (x i)) * g (fun i => f i (x i))) =
                  ∑ y : ι → β, (∏ i, ∑ a : α, if f i a = y i then w i a else 0) * g y := by
                intro ι α β _ _ _ _ _ w f g
                simp_rw [Fintype.prod_sum, Finset.sum_mul]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro x _
                have he : ∀ y : ι → β, (∏ i, if f i (x i) = y i then w i (x i) else 0) =
                    if (fun i => f i (x i)) = y then ∏ i, w i (x i) else 0 := by
                  intro y
                  by_cases h : (fun i => f i (x i)) = y
                  · subst y; simp
                  · rw [if_neg h]
                    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
                    apply Finset.prod_eq_zero (Finset.mem_univ i)
                    simp [hi]
                simp_rw [he, ite_mul, zero_mul]
                simp
              have center : ∀ (β : Type) [Fintype β] [DecidableEq β] [Nonempty β]
                  (n : ℕ) (q : Fin n → (Fin n → β) → ℝ)
                  (hd : ∀ s τ τ', (∀ u, u ≤ s → τ u = τ' u) → q s τ = q s τ')
                  (hn : ∀ s τ, ∑ a, q s (Function.update τ s a) = 1)
                  (s : Fin n) (f : (Fin n → β) → ℝ),
                  (∀ τ τ', (∀ u, u ≤ s → τ u = τ' u) → f τ = f τ') →
                  (∀ τ, ∑ a, q s (Function.update τ s a) * f (Function.update τ s a) = 0) →
                  ∑ τ, (∏ u, q u τ) * f τ = 0 := by
                intro β _ _ _ n q hd hn s f hfd hfn
                let q' : Fin n → (Fin n → β) → ℝ := fun u τ => q u τ * if u = s then 1 + f τ else 1
                have hdn : ∀ u τ τ', (∀ v, v ≤ u → τ v = τ' v) → q' u τ = q' u τ' := by
                  intro u τ τ' hh
                  dsimp [q']
                  rw [hd u τ τ' hh]
                  by_cases hu : u = s
                  · subst u; rw [hfd τ τ' hh]
                  · simp [hu]
                have hnn : ∀ u τ, ∑ a, q' u (Function.update τ u a) = 1 := by
                  intro u τ
                  by_cases hu : u = s
                  · subst u
                    simp only [q', ↓reduceIte, mul_add, mul_one, Finset.sum_add_distrib, hn, hfn, add_zero]
                  · simpa [q', hu] using hn u τ
                have hh := gen β n q' hdn hnn
                have he : ∀ τ, (∏ u, q' u τ) = (∏ u, q u τ) * (1 + f τ) := by
                  intro τ
                  dsimp only [q']
                  rw [Finset.prod_mul_distrib]
                  simp
                simp_rw [he, mul_add, mul_one] at hh
                rw [Finset.sum_add_distrib, gen β n q hd hn] at hh
                linarith
              have marginal : ∀ (ι α : Type) [Fintype ι] [Fintype α] [DecidableEq ι]
                  [DecidableEq α] (w : ι → α → ℝ), (∀ i, ∑ a, w i a = 1) →
                  ∀ (i : ι) (a : α), (∑ x : ι → α, (∏ k, w k (x k)) *
                    (if x i = a then 1 else 0)) = w i a := by
                intro ι α _ _ _ _ w hw i a
                have he : ∀ x : ι → α, (∏ k, w k (x k)) * (if x i = a then 1 else 0) =
                    ∏ k, w k (x k) * (if k = i then (if x k = a then 1 else 0) else 1) := by
                  intro x
                  rw [Finset.prod_mul_distrib]
                  simp
                simp_rw [he]
                rw [← Fintype.prod_sum (fun k b => w k b * (if k = i then (if b = a then 1 else 0) else 1))]
                have hs : ∀ k, (∑ b, w k b * (if k = i then (if b = a then 1 else 0) else 1)) =
                    if k = i then w k a else 1 := by
                  intro k
                  by_cases hk : k = i
                  · subst k; simp
                  · simp [hk, hw]
                simp_rw [hs]
                simp
              have marginalE : ∀ (ι α : Type) [Fintype ι] [Fintype α] [DecidableEq ι]
                  [DecidableEq α] (w : ι → α → ℝ), (∀ i, ∑ a, w i a = 1) →
                  ∀ (i : ι) (g : α → ℝ), (∑ x : ι → α, (∏ k, w k (x k)) * g (x i)) =
                    ∑ a, w i a * g a := by
                intro ι α _ _ _ _ w hw i g
                have hg : ∀ x : ι → α, g (x i) = ∑ a, (if x i = a then (1:ℝ) else 0) * g a := by
                  intro x; simp
                conv_lhs => arg 2; ext x; rw [hg x, Finset.mul_sum]
                rw [Finset.sum_comm]
                simp_rw [← mul_assoc, ← Finset.sum_mul, marginal ι α w hw]
              let bern : ℝ → MeasureTheory.Measure ℝ := fun p =>
                ENNReal.ofReal p • MeasureTheory.Measure.dirac (1:ℝ) +
                  ENNReal.ofReal (1-p) • MeasureTheory.Measure.dirac (0:ℝ)
              have bern_prob : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → MeasureTheory.IsProbabilityMeasure (bern p) := by
                intro p hp hp1
                constructor
                simp [bern, MeasureTheory.Measure.add_apply]
                rw [← ENNReal.ofReal_add hp (by linarith)]
                simp
              have bern_supp : ∀ p : ℝ, bern p (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
                intro p
                simp [bern, MeasureTheory.Measure.add_apply]
              have bern_mean : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∫ x, x ∂(bern p) = p := by
                intro p hp hp1
                rw [MeasureTheory.integral_add_measure, MeasureTheory.integral_smul_measure,
                  MeasureTheory.integral_smul_measure]
                · simp [ENNReal.toReal_ofReal hp]
                · exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp)
                · exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp)
              refine ⟨1/128, by norm_num, ?_⟩
              intro K _ hK
              refine ⟨K, by omega, ?_⟩
              intro T hT
              have hTpos : (0:ℝ) < T := by exact_mod_cast (show 0 < T by omega)
              have hKpos : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
              set ε : ℝ := Real.sqrt ((K:ℝ) / T) / 32 with hε
              have hε0 : 0 ≤ ε := by positivity
              have hε1 : ε ≤ 1/32 := by
                have : Real.sqrt ((K:ℝ)/T) ≤ 1 := by
                  rw [Real.sqrt_le_one]
                  rw [div_le_one hTpos]; exact_mod_cast hT
                rw [hε]; linarith
              let pr : Fin K → Fin K → ℝ := fun j i => 1/2 + if i = j then ε else 0
              have pr0 : ∀ j i, 0 ≤ pr j i := by intro j i; simp only [pr]; split_ifs <;> linarith
              have pr1 : ∀ j i, pr j i ≤ 1 := by intro j i; simp only [pr]; split_ifs <;> linarith
              have hbp : ∀ j i, MeasureTheory.IsProbabilityMeasure (bern (pr j i)) :=
                fun j i => bern_prob _ (pr0 j i) (pr1 j i)
              let S : Fin K → StochInstance K 1 := fun j =>
                { D := fun _ => 1
                  F := fun i _ => bern (pr j i)
                  D_dist := ⟨fun _ => zero_le_one, by simp⟩
                  F_prob := fun i _ => hbp j i
                  F_supp := fun i _ => bern_supp _
                  roundLaw := fun _ => MeasureTheory.Measure.pi
                    (fun i : Fin K => MeasureTheory.Measure.pi (fun c : Fin 1 => bern (pr j i)))
                  round_prob := fun _ => inferInstance
                  round_marginal := by
                    intro t i c
                    have h1 := (MeasureTheory.measurePreserving_eval
                      (fun i : Fin K => MeasureTheory.Measure.pi (fun c : Fin 1 => bern (pr j i))) i)
                    have h2 := (MeasureTheory.measurePreserving_eval (fun c : Fin 1 => bern (pr j i)) c)
                    have := h2.comp h1
                    exact this.map_eq }
              refine ⟨K, by omega, S, fun j t => rfl, ?_⟩
              have R1 : ∀ (μ : Fin T → Fin K → Fin 1 → MeasureTheory.Measure Bool)
                  [∀ t i c, MeasureTheory.IsProbabilityMeasure (μ t i c)]
                  (g : (Fin T → Fin K → Fin 1 → ℝ) → ℝ),
                  ∫ r, g r ∂(MeasureTheory.Measure.pi fun t => MeasureTheory.Measure.pi fun i =>
                    MeasureTheory.Measure.pi fun c =>
                    MeasureTheory.Measure.map (fun b : Bool => if b then (1:ℝ) else 0) (μ t i c)) =
                  ∑ b : Fin T → Fin K → Fin 1 → Bool, (∏ t, ∏ i, ∏ c, (μ t i c).real {b t i c}) *
                    g (fun t i c => if b t i c then 1 else 0) := by
                intro μ _ g
                open MeasureTheory in
                  have e1 : ∀ t i, (Measure.pi fun c => Measure.map (fun b : Bool => if b then (1:ℝ) else 0) (μ t i c))
                     = Measure.map (fun x c => if x c then (1:ℝ) else 0) (Measure.pi fun c => μ t i c) := by
                    intro t i
                    exact (Measure.pi_map_pi (f := fun _ (b : Bool) => if b then (1:ℝ) else 0)
                      (fun c => (measurable_of_countable _).aemeasurable)).symm
                  simp_rw [e1]
                  have e2 : ∀ t, (Measure.pi fun i => Measure.map (fun x c => if x c then (1:ℝ) else 0) (Measure.pi fun c => μ t i c))
                     = Measure.map (fun y i c => if y i c then (1:ℝ) else 0) (Measure.pi fun i => Measure.pi fun c => μ t i c) := by
                    intro t
                    exact (Measure.pi_map_pi (f := fun _ (x : Fin 1 → Bool) c => if x c then (1:ℝ) else 0)
                      (fun c => (measurable_of_countable _).aemeasurable)).symm
                  simp_rw [e2]
                  rw [← Measure.pi_map_pi (f := fun _ (y : Fin K → Fin 1 → Bool) i c => if y i c then (1:ℝ) else 0)
                      (fun c => (measurable_of_countable _).aemeasurable)]
                  have hemb : MeasurableEmbedding (fun (b : Fin T → Fin K → Fin 1 → Bool) t i c => if b t i c then (1:ℝ) else 0) := by
                    apply MeasurableEmbedding.of_measurable_inverse_on_range (measurable_of_countable _)
                      (Set.finite_range _).measurableSet
                      (g := fun (x : Set.range (fun (b : Fin T → Fin K → Fin 1 → Bool) t i c => if b t i c then (1:ℝ) else 0)) t i c => decide (x.1 t i c = 1))
                    · apply measurable_pi_lambda; intro t; apply measurable_pi_lambda; intro i
                      apply measurable_pi_lambda; intro c
                      apply measurable_to_countable'
                      intro x
                      have hm := ((measurable_pi_apply c).comp ((measurable_pi_apply i).comp ((measurable_pi_apply t).comp
                        (measurable_subtype_coe (p := (· ∈ Set.range (fun (b : Fin T → Fin K → Fin 1 → Bool) t i c => if b t i c then (1:ℝ) else 0))))))) (measurableSet_singleton (1:ℝ))
                      cases x
                      · convert hm.compl using 1; ext y; simp
                      · convert hm using 1; ext y; simp
                    · intro b; ext t i c; simp
                  rw [hemb.integral_map, integral_fintype Integrable.of_finite]
                  congr 1; ext b
                  rw [smul_eq_mul]
                  congr 1
                  rw [measureReal_def, ← Set.univ_pi_singleton b, Measure.pi_pi, ENNReal.toReal_prod]
                  refine Finset.prod_congr rfl (fun t _ => ?_)
                  rw [← Set.univ_pi_singleton (b t), Measure.pi_pi, ENNReal.toReal_prod]
                  refine Finset.prod_congr rfl (fun i _ => ?_)
                  rw [← Set.univ_pi_singleton (b t i), Measure.pi_pi, ENNReal.toReal_prod]
                  rfl
              let bernB : ℝ → MeasureTheory.Measure Bool := fun p =>
                ENNReal.ofReal p • MeasureTheory.Measure.dirac true +
                  ENNReal.ofReal (1-p) • MeasureTheory.Measure.dirac false
              have hbern : ∀ p, bern p = MeasureTheory.Measure.map (fun b : Bool => if b then (1:ℝ) else 0) (bernB p) := by
                intro p
                simp only [bern, bernB]
                rw [MeasureTheory.Measure.map_add _ _ (by fun_prop), MeasureTheory.Measure.map_smul,
                  MeasureTheory.Measure.map_smul,
                  MeasureTheory.Measure.map_dirac' (measurable_of_countable _),
                  MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]
                simp
              have bernB_prob : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → MeasureTheory.IsProbabilityMeasure (bernB p) := by
                intro p hp hp1
                constructor
                simp [bernB, MeasureTheory.Measure.add_apply]
                rw [← ENNReal.ofReal_add hp (by linarith)]
                simp
              have bernB_real : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ x : Bool, (bernB p).real {x} = if x then p else 1 - p := by
                intro p hp hp1 x
                cases x <;> simp [bernB, MeasureTheory.measureReal_def, MeasureTheory.Measure.add_apply,
                  ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal (show 0 ≤ 1 - p by linarith)]
              let W : Fin K → (Fin T → Fin K → Fin 1 → Bool) → ℝ := fun j b =>
                ∏ t, ∏ i, ∏ c, (if b t i c then pr j i else 1 - pr j i)
              let emb : (Fin T → Fin K → Fin 1 → Bool) → (Fin T → Fin K → Fin 1 → ℝ) :=
                fun b t i c => if b t i c then 1 else 0
              have hfin : ∀ j (g : (Fin T → Fin K → Fin 1 → ℝ) → ℝ),
                  ∫ r, g r ∂((S j).tableLaw T) = ∑ b, W j b * g (emb b) := by
                intro j g
                have : (S j).tableLaw T = MeasureTheory.Measure.pi fun t => MeasureTheory.Measure.pi fun i =>
                    MeasureTheory.Measure.pi fun c =>
                    MeasureTheory.Measure.map (fun b : Bool => if b then (1:ℝ) else 0) (bernB (pr j i)) := by
                  simp only [StochInstance.tableLaw, S, hbern]
                rw [this]
                have hP : ∀ (t : Fin T) (i : Fin K) (c : Fin 1), MeasureTheory.IsProbabilityMeasure (bernB (pr j i)) :=
                  fun t i c => bernB_prob _ (pr0 j i) (pr1 j i)
                rw [@R1 (fun t i c => bernB (pr j i)) hP g]
                refine Finset.sum_congr rfl (fun b _ => ?_)
                simp only [W, emb, bernB_real _ (pr0 j _) (pr1 j _)]
              let w : Fin K → Fin K → Bool → ℝ := fun j i b => if b then pr j i else 1 - pr j i
              have wsum : ∀ j i, ∑ b : Bool, w j i b = 1 := by
                intro j i; simp [w]
              have wpos : ∀ j i b, 0 < w j i b := by
                intro j i b; cases b <;> dsimp [w, pr] <;> split_ifs <;> linarith
              have hproj : ∀ (j i : Fin K) (c : Fin 1) (x : Bool),
                  (∑ v : Fin K → Fin 1 → Bool, (∏ k, ∏ d, w j k (v k d)) *
                    (if v i c = x then (1:ℝ) else 0)) = w j i x := by
                intro j i c x
                have hn : ∀ k, ∑ v : Fin 1 → Bool, ∏ d, w j k (v d) = 1 := by
                  intro k
                  rw [← Fintype.prod_sum]
                  simp_rw [wsum]
                  simp
                rw [marginalE (Fin K) (Fin 1 → Bool) (fun k v => ∏ d, w j k (v d)) hn i
                  (fun v => if v c = x then 1 else 0)]
                exact marginal (Fin 1) Bool (fun _ => w j i) (fun _ => wsum j i) c x
              have project : ∀ (j : Fin K) (τ : Fin T → Fin 1 × Fin K) (g : (Fin T → Bool) → ℝ),
                  (∑ b, W j b * g (fun s => b s (τ s).2 (τ s).1)) =
                    ∑ x : Fin T → Bool, (∏ s, w j (τ s).2 (x s)) * g x := by
                intro j τ g
                change (∑ b : Fin T → Fin K → Fin 1 → Bool, (∏ s : Fin T, ∏ i : Fin K, ∏ c : Fin 1, w j i (b s i c)) *
                  g (fun s => b s (τ s).2 (τ s).1)) = _
                refine (push (Fin T) (Fin K → Fin 1 → Bool) Bool
                  (fun _ v => ∏ i, ∏ c, w j i (v i c)) (fun s v => v (τ s).2 (τ s).1) g).trans ?_
                apply Finset.sum_congr rfl
                intro x _
                congr 1
                apply Finset.prod_congr rfl
                intro s _
                simpa only [mul_ite, mul_one, mul_zero] using hproj j (τ s).2 (τ s).1 (x s)
              intro A hAv hAm t
              unfold Policy at A
              let B : Type := (Fin 1 × Fin K) × Bool
              let H : (s : Fin T) → (Fin T → B) → Fin s → Obs K 1 := fun s z u =>
                let v := z ⟨u.val, lt_trans u.isLt s.isLt⟩
                (v.1.1, v.1.2, fun _ => if v.2 then 1 else 0)
              let a : Fin T → (Fin T → B) → ℝ := fun s z => A s (H s z) (z s).1.1 (z s).1.2
              let q : (Fin K → Bool → ℝ) → Fin T → (Fin T → B) → ℝ :=
                fun p s z => a s z * p (z s).1.2 (z s).2
              let Q : (Fin K → Bool → ℝ) → (Fin T → B) → ℝ := fun p z => ∏ s, q p s z
              have Hd : ∀ (s : Fin T) (z z' : Fin T → B),
                  (∀ u, u < s → z u = z' u) → H s z = H s z' := by
                intro s z z' hh
                funext u
                dsimp only [H]
                rw [hh ⟨u.val, lt_trans u.isLt s.isLt⟩ (by exact u.isLt)]
              have Hu : ∀ (s : Fin T) (z : Fin T → B) (v : B), H s (Function.update z s v) = H s z := by
                intro s z v
                apply Hd
                intro u hu
                exact Function.update_of_ne (ne_of_lt hu) v z
              have qd : ∀ p s z z', (∀ u, u ≤ s → z u = z' u) → q p s z = q p s z' := by
                intro p s z z' hh
                dsimp only [q, a]
                rw [Hd s z z' (fun u hu => hh u hu.le), hh s le_rfl]
              have qu : ∀ p s z (v : B), q p s (Function.update z s v) =
                  A s (H s z) v.1.1 v.1.2 * p v.1.2 v.2 := by
                intro p s z v
                simp only [q, a, Hu, Function.update_self]
              have qn : ∀ p : Fin K → Bool → ℝ, (∀ i, ∑ b, p i b = 1) →
                  ∀ s z, ∑ v : B, q p s (Function.update z s v) = 1 := by
                intro p hp s z
                simp_rw [qu]
                dsimp only [B]
                rw [Fintype.sum_prod_type]
                simp_rw [← Finset.mul_sum, hp, mul_one]
                rw [Fintype.sum_prod_type, Fin.sum_univ_one]
                exact hAv.2 _ _ _
              have Qn : ∀ p : Fin K → Bool → ℝ, (∀ i, ∑ b, p i b = 1) → ∑ z, Q p z = 1 := by
                intro p hp
                exact gen B T (q p) (qd p) (qn p hp)
              have Qpos : ∀ (p : Fin K → Bool → ℝ), (∀ i b, 0 ≤ p i b) → ∀ z, 0 ≤ Q p z := by
                intro p hp z
                apply Finset.prod_nonneg
                intro s _
                exact mul_nonneg (hAv.1 _ _ _ _) (hp _ _)
              have thist : ∀ (b : Fin T → Fin K → Fin 1 → Bool) (τ : Fin T → Fin 1 × Fin K) s,
                  hist (fun _ _ _ => True) (emb b) τ s =
                    H s (fun u => (τ u, b u (τ u).2 (τ u).1)) := by
                intro b τ s
                funext u
                dsimp only [hist, H]
                apply congrArg (fun f : Fin 1 → ℝ =>
                  ((τ (Fin.castLE s.isLt.le u)).1, (τ (Fin.castLE s.isLt.le u)).2, f))
                funext c
                dsimp [feedback, emb]
                have hc : c = (τ (Fin.castLE s.isLt.le u)).1 := Subsingleton.elim _ _
                rw [hc]
                simp [Fin.castLE]
              have lift : ∀ (j : Fin K)
                  (X : (Fin T → Fin 1 × Fin K) → (Fin T → Bool) → ℝ),
                  (∑ b, W j b * ∑ τ, trajProb (fun _ _ _ => True) (S j).D A (emb b) τ *
                    X τ (fun s => b s (τ s).2 (τ s).1)) =
                  ∑ z : Fin T → B, Q (w j) z * X (fun s => (z s).1) (fun s => (z s).2) := by
                intro j X
                simp_rw [Finset.mul_sum]
                rw [Finset.sum_comm]
                have he : ∀ (τ : Fin T → Fin 1 × Fin K),
                    (∑ b, W j b * (trajProb (fun _ _ _ => True) (S j).D A (emb b) τ *
                      X τ (fun s => b s (τ s).2 (τ s).1))) =
                    ∑ x : Fin T → Bool, Q (w j) (fun s => (τ s, x s)) * X τ x := by
                  intro τ
                  have hh : ∀ b, trajProb (fun _ _ _ => True) (S j).D A (emb b) τ =
                      ∏ s, a s (fun u => (τ u, b u (τ u).2 (τ u).1)) := by
                    intro b
                    unfold trajProb
                    apply Finset.prod_congr rfl
                    intro s _
                    rw [thist]
                    simp only [S, one_mul, a]
                  simp_rw [hh]
                  rw [project j τ (fun x => (∏ s, a s (fun u => (τ u, x u))) * X τ x)]
                  apply Finset.sum_congr rfl
                  intro x _
                  dsimp only [Q, q]
                  rw [Finset.prod_mul_distrib]
                  ring
                simp_rw [he]
                rw [← Fintype.sum_prod_type (fun v : (Fin T → Fin 1 × Fin K) × (Fin T → Bool) =>
                  Q (w j) (fun s => (v.1 s, v.2 s)) * X v.1 v.2)]
                simpa only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk] using
                  (Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => Fin 1 × Fin K)
                  (fun _ => Bool)).symm.sum_comp
                    (fun z => Q (w j) z * X (fun s => (z s).1) (fun s => (z s).2))
              let P : Fin K → ℝ := fun j => ∑ z, Q (w j) z *
                (if (z t).1.2 = j then (1:ℝ) else 0)
              have hsup : ∀ j : Fin K, (∑ d, (S j).D d * Finset.univ.sup' Finset.univ_nonempty
                  (fun i => (S j).mean i d)) = 1/2 + ε := by
                intro j
                rw [Fin.sum_univ_one]
                have hm : ∀ i d, (S j).mean i d = pr j i := fun i d => bern_mean _ (pr0 j i) (pr1 j i)
                have hD : (S j).D 0 = 1 := rfl
                simp only [hm, hD, one_mul]
                apply le_antisymm
                · apply Finset.sup'_le
                  intro i _
                  simp only [pr]; split_ifs <;> linarith
                · have := Finset.le_sup' (fun i => pr j i) (Finset.mem_univ j)
                  have e : pr j j = 1/2 + ε := by simp [pr]
                  rw [e] at this; exact this
              have hearn : ∀ j, ∫ r, expect (fun _ _ _ => True) (S j).D A r
                  (fun τ => r t (τ t).2 (τ t).1) ∂((S j).tableLaw T) = 1/2 + ε * P j := by
                intro j
                rw [hfin j]
                change (∑ b, W j b * ∑ τ, trajProb (fun _ _ _ => True) (S j).D A (emb b) τ *
                  (if b t (τ t).2 (τ t).1 then (1:ℝ) else 0)) = _
                rw [lift j (fun _ x => if x t then 1 else 0)]
                have hc : (∑ z, Q (w j) z * ((if (z t).2 then (1:ℝ) else 0) - pr j (z t).1.2)) = 0 := by
                  apply center B T (q (w j)) (qd _) (qn _ (wsum j)) t
                  · intro z z' hh
                    rw [hh t le_rfl]
                  · intro z
                    simp_rw [qu, Function.update_self]
                    dsimp only [B]
                    rw [Fintype.sum_prod_type]
                    apply Finset.sum_eq_zero
                    intro v _
                    simp only [Fintype.sum_bool, w, Bool.false_eq_true, ↓reduceIte]
                    ring
                have hn := Qn (w j) (wsum j)
                have he : ∀ z : Fin T → B, pr j (z t).1.2 =
                    1/2 + ε * (if (z t).1.2 = j then (1:ℝ) else 0) := by
                  intro z; dsimp [pr]; split_ifs <;> ring
                simp_rw [mul_sub, he, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  ← Finset.sum_mul, hn] at hc
                dsimp only [P]
                have he' : (∑ z : Fin T → B, Q (w j) z * (ε * if (z t).1.2 = j then 1 else 0)) = ε * P j := by
                  dsimp only [P]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro z _
                  ring
                rw [he'] at hc
                linarith
              have key1 : ∀ j, roundStochRegret t (fun _ _ _ => True) (S j) A = ε * (1 - P j) := by
                intro j
                unfold roundStochRegret
                rw [hsup j, hearn j]; ring
              have key2 : ∑ j, P j ≤ 3 / 4 * (K:ℝ) := by
                let U : (Fin T → B) → ℝ := Q (fun _ _ => 1/2)
                let ell : Fin K → B → ℝ := fun j v => 2 * w j v.1.2 v.2
                let L : Fin K → (Fin T → B) → ℝ := fun j z => ∏ s, ell j (z s)
                let D : Fin K → ℝ := fun j => ∑ z, U z * (-Real.log (L j z))
                have Un : ∑ z, U z = 1 := by
                  exact Qn (fun _ _ => 1/2) (by intro i; norm_num)
                have Up : ∀ z, 0 ≤ U z := Qpos (fun _ _ => 1/2) (by intros; norm_num)
                have ep : ∀ j v, 0 < ell j v := by
                  intro j v
                  exact mul_pos (by norm_num) (wpos _ _ _)
                have Lp : ∀ j z, 0 < L j z := by
                  intro j z
                  exact Finset.prod_pos (fun s _ => ep j (z s))
                have QL : ∀ j z, Q (w j) z = U z * L j z := by
                  intro j z
                  dsimp only [U, L, Q]
                  rw [← Finset.prod_mul_distrib]
                  apply Finset.prod_congr rfl
                  intro s _
                  dsimp only [q, ell]
                  ring
                have ULn : ∀ j, ∑ z, U z * L j z = 1 := by
                  intro j
                  simp_rw [← QL]
                  exact Qn _ (wsum j)
                have hp : 0 < 1 + 2 * ε := by linarith
                have hm : 0 < 1 - 2 * ε := by linarith
                let g : Bool → ℝ := fun b => if b then -Real.log (1 + 2 * ε) else -Real.log (1 - 2 * ε)
                let d : ℝ := (g true + g false) / 2
                have es : ∀ j (v : B), ell j v = if v.1.2 = j then
                    (if v.2 then 1 + 2 * ε else 1 - 2 * ε) else 1 := by
                  intro j v
                  rcases v with ⟨⟨c, i⟩, b⟩
                  cases b <;> dsimp [ell, w, pr] <;> split_ifs <;> ring
                have sl : ∀ v : B, ∑ j, -Real.log (ell j v) = g v.2 := by
                  intro v
                  have ee : ∀ j, -Real.log (ell j v) = if v.1.2 = j then g v.2 else 0 := by
                    intro j
                    rw [es]
                    by_cases hv : v.1.2 = j <;> cases hb : v.2 <;> simp [hv, g, hb]
                  simp_rw [ee]
                  simp [eq_comm]
                have logL : ∀ j z, -Real.log (L j z) = ∑ s, -Real.log (ell j (z s)) := by
                  intro j z
                  dsimp only [L]
                  rw [Real.log_prod (fun s _ => (ep j (z s)).ne')]
                  simp only [Finset.sum_neg_distrib]
                have Eg : ∀ s : Fin T, ∑ z, U z * g (z s).2 = d := by
                  intro s
                  have hc : (∑ z, U z * (g (z s).2 - d)) = 0 := by
                    apply center B T (q (fun _ _ => 1/2)) (qd (fun _ _ => 1/2)) (qn (fun _ _ => 1/2) (by intro i; norm_num)) s
                    · intro z z' hh; rw [hh s le_rfl]
                    · intro z
                      simp_rw [qu, Function.update_self]
                      dsimp only [B]
                      rw [Fintype.sum_prod_type]
                      apply Finset.sum_eq_zero
                      intro v _
                      simp only [Fintype.sum_bool]
                      dsimp only [d]
                      ring
                  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Un] at hc
                  linarith
                have Ds : ∑ j, D j = (T : ℝ) * d := by
                  dsimp only [D]
                  rw [Finset.sum_comm]
                  simp_rw [logL, Finset.mul_sum]
                  conv_lhs => arg 2; ext z; rw [Finset.sum_comm]
                  simp_rw [← Finset.mul_sum, sl]
                  simp_rw [Finset.mul_sum]
                  rw [Finset.sum_comm]
                  simp_rw [Eg]
                  simp
                have de : d = -(1/2 : ℝ) * Real.log (1 - 4 * ε^2) := by
                  dsimp only [d, g]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [show 1 - 4 * ε^2 = (1 + 2 * ε) * (1 - 2 * ε) by ring,
                    Real.log_mul hp.ne' hm.ne']
                  ring
                have hd : d ≤ 4 * ε^2 := by
                  have he2 : ε^2 ≤ 1/1024 := by nlinarith
                  have hz : 0 < 1 - 4 * ε^2 := by nlinarith
                  have hh := Real.log_le_sub_one_of_pos (inv_pos.2 hz)
                  rw [Real.log_inv] at hh
                  have hdiv : (1 - 4 * ε^2)⁻¹ ≤ 1 + 8 * ε^2 := by
                    rw [inv_eq_one_div, div_le_iff₀ hz]
                    nlinarith [sq_nonneg ε, sq_nonneg (ε^2)]
                  rw [de]
                  linarith
                have hscale : ε^2 * (T : ℝ) = (K : ℝ) / 1024 := by
                  have hs := Real.sq_sqrt (div_nonneg hKpos.le hTpos.le)
                  have he : Real.sqrt ((K:ℝ)/T) = 32 * ε := by rw [hε]; ring
                  rw [he] at hs
                  have hh := (eq_div_iff hTpos.ne').1 hs
                  nlinarith
                have Db : ∑ j, D j ≤ (K : ℝ) / 256 := by
                  rw [Ds]
                  have hh := mul_le_mul_of_nonneg_left hd hTpos.le
                  nlinarith [hscale]
                have tvscalar : ∀ x : ℝ, 0 < x →
                    x - 1 ≤ 32 * (x - 1 - Real.log x) + (x + 1) / 32 := by
                  intro x hx
                  have hr := Real.sq_sqrt hx.le
                  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
                  rw [Real.log_sqrt hx.le] at hl
                  have hs := sq_nonneg (32 * (Real.sqrt x - 1) - (Real.sqrt x + 1) / 2)
                  nlinarith [sq_nonneg (Real.sqrt x - 1)]
                let P0 : Fin K → ℝ := fun j => ∑ z, U z * (if (z t).1.2 = j then (1:ℝ) else 0)
                have P0n : ∑ j, P0 j = 1 := by
                  dsimp only [P0]
                  rw [Finset.sum_comm]
                  simp_rw [← Finset.mul_sum]
                  simpa using Un
                have Pb : ∀ j, P j ≤ P0 j + 32 * D j + 1/16 := by
                  intro j
                  have hs : ∀ z : Fin T → B,
                      U z * L j z * (if (z t).1.2 = j then (1:ℝ) else 0) ≤
                      U z * (if (z t).1.2 = j then (1:ℝ) else 0) +
                      32 * (U z * (L j z - 1 - Real.log (L j z))) + U z * (L j z + 1) / 32 := by
                    intro z
                    have hh := tvscalar (L j z) (Lp j z)
                    have hh0 := Real.log_le_sub_one_of_pos (Lp j z)
                    have hn : 0 ≤ 32 * (L j z - 1 - Real.log (L j z)) + (L j z + 1) / 32 := by
                      linarith [Lp j z]
                    by_cases he : (z t).1.2 = j
                    · simp only [if_pos he, mul_one]
                      nlinarith [mul_nonneg (Up z) (by linarith : 0 ≤ 32 *
                        (L j z - 1 - Real.log (L j z)) + (L j z + 1) / 32 - (L j z - 1))]
                    · simp only [if_neg he, mul_zero, zero_add]
                      nlinarith [mul_nonneg (Up z) hn]
                  have hh := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hs z)
                  dsimp only [P]
                  simp_rw [QL]
                  have he : (∑ z, U z * (L j z - 1 - Real.log (L j z))) = D j := by
                    dsimp only [D]
                    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
                    rw [ULn j, Un]
                    simp only [mul_neg, Finset.sum_neg_distrib]
                    ring
                  have he' : (∑ z, U z * (L j z + 1) / 32) = 1/16 := by
                    simp only [mul_add, mul_one]
                    rw [← Finset.sum_div, Finset.sum_add_distrib, ULn j, Un]
                    norm_num
                  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, he, he'] at hh
                  exact hh
                have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => Pb j)
                simp only [Finset.sum_add_distrib, ← Finset.mul_sum, P0n, Finset.sum_const,
                  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
                have hK2 : (2:ℝ) ≤ K := by exact_mod_cast hK
                linarith
              simp only [key1]
              rw [← Finset.mul_sum, Finset.sum_sub_distrib]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
              have hsq : Real.sqrt ((K:ℝ)/T) = 32 * ε := by rw [hε]; ring
              rw [hsq]
              have : (1:ℝ) / K * (ε * (K - ∑ j, P j)) = ε * (1 - (∑ j, P j) / K) := by
                field_simp
              rw [this]
              have h3 : (∑ j, P j) / K ≤ 3/4 := by
                rw [div_le_iff₀ hKpos]; linarith
              nlinarith
