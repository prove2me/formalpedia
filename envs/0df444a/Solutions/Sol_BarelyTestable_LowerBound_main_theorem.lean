-- Prove2me | solution 1 for BarelyTestable.LowerBound.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:31:52.001189+00:00
-- url     : https://prove2.me/submissions/7c7c0304-1565-4913-9c91-19bac9e96e01

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Protocol
import Theorems.Thm_BarelyTestable_LowerBound_yao
import Theorems.Thm_BarelyTestable_LowerBound_completeness
import Theorems.Thm_BarelyTestable_LowerBound_soundness
import Theorems.Thm_BarelyTestable_LowerBound_indistinguishability
set_option autoImplicit false
set_option linter.unusedSectionVars false
open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTMain

variable {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- Preimage of a vertex along a coordinate embedding. -/
def pre (ρ : ι ↪ ι') (S : Finset ι') : Finset ι := Finset.univ.filter (fun i => ρ i ∈ S)

lemma pre_union (ρ : ι ↪ ι') (S T : Finset ι') : pre ρ (S ∪ T) = pre ρ S ∪ pre ρ T := by
  ext i; simp [pre]

lemma pre_inter (ρ : ι ↪ ι') (S T : Finset ι') : pre ρ (S ∩ T) = pre ρ S ∩ pre ρ T := by
  ext i; simp [pre]

lemma submodular_comp_pre (ρ : ι ↪ ι') (f : Oracle ι) (hf : Submodular f) :
    Submodular (fun S => f (pre ρ S)) := by
  intro S T
  simp only [pre_union, pre_inter]
  exact hf _ _

/-- complement coordinates -/
abbrev Rest (ρ : ι ↪ ι') := {x : ι' // x ∉ Set.range ρ}

def glue (ρ : ι ↪ ι') (T : Finset ι) (Z : Finset (Rest ρ)) : Finset ι' :=
  T.map ρ ∪ Z.map (Function.Embedding.subtype _)

def restPart (ρ : ι ↪ ι') (S : Finset ι') : Finset (Rest ρ) :=
  Finset.univ.filter (fun z => z.1 ∈ S)

lemma pre_glue (ρ : ι ↪ ι') (T : Finset ι) (Z : Finset (Rest ρ)) : pre ρ (glue ρ T Z) = T := by
  ext i
  simp only [pre, glue, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro (⟨j, hj, hji⟩ | ⟨z, _, hz⟩)
    · rwa [← ρ.injective hji]
    · exact absurd ⟨i, hz.symm⟩ z.2
  · intro hi; exact Or.inl ⟨i, hi, rfl⟩

lemma restPart_glue (ρ : ι ↪ ι') (T : Finset ι) (Z : Finset (Rest ρ)) :
    restPart ρ (glue ρ T Z) = Z := by
  ext z
  simp only [restPart, glue, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro (⟨j, _, hj⟩ | ⟨w, hw, hwz⟩)
    · exact absurd ⟨j, hj⟩ z.2
    · rwa [← Subtype.ext hwz]
  · intro hz; exact Or.inr ⟨z, hz, rfl⟩

lemma glue_pre_restPart (ρ : ι ↪ ι') (S : Finset ι') : glue ρ (pre ρ S) (restPart ρ S) = S := by
  ext x
  simp only [pre, glue, restPart, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact hj
    · exact hw
  · intro hx
    by_cases hr : x ∈ Set.range ρ
    · obtain ⟨j, rfl⟩ := hr; exact Or.inl ⟨j, hx, rfl⟩
    · exact Or.inr ⟨⟨x, hr⟩, hx, rfl⟩

def glueEquiv (ρ : ι ↪ ι') : Finset ι × Finset (Rest ρ) ≃ Finset ι' where
  toFun p := glue ρ p.1 p.2
  invFun S := (pre ρ S, restPart ρ S)
  left_inv p := by simp [pre_glue, restPart_glue]
  right_inv S := glue_pre_restPart ρ S

lemma glue_union (ρ : ι ↪ ι') (T₁ T₂ : Finset ι) (Z : Finset (Rest ρ)) :
    glue ρ T₁ Z ∪ glue ρ T₂ Z = glue ρ (T₁ ∪ T₂) Z := by
  ext x; simp only [glue, Finset.mem_union, Finset.map_union]; tauto

lemma glue_inter (ρ : ι ↪ ι') (T₁ T₂ : Finset ι) (Z : Finset (Rest ρ)) :
    glue ρ T₁ Z ∩ glue ρ T₂ Z = glue ρ (T₁ ∩ T₂) Z := by
  apply (glueEquiv ρ).symm.injective
  simp only [glueEquiv, Equiv.coe_fn_symm_mk, Prod.mk.injEq]
  constructor
  · rw [pre_inter, pre_glue, pre_glue, pre_glue]
  · rw [restPart_glue]
    ext z
    simp only [restPart, glue, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Finset.mem_union, Finset.mem_map, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨h1, _⟩
      rcases h1 with ⟨j, _, hj⟩ | ⟨w, hw, hwz⟩
      · exact absurd ⟨j, hj⟩ z.2
      · rwa [← Subtype.ext hwz]
    · intro hz
      exact ⟨Or.inr ⟨z, hz, rfl⟩, Or.inr ⟨z, hz, rfl⟩⟩

lemma mismatch_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (f g : Oracle κ) :
    (mismatch f g : ℝ) = ∑ S : Finset κ, if f S ≠ g S then (1 : ℝ) else 0 := by
  classical
  unfold mismatch
  rw [Finset.card_filter]
  push_cast
  rfl

lemma far_comp_pre (ρ : ι ↪ ι') (f : Oracle ι) (δ : ℝ) (hf : Far Submodular δ f) :
    Far Submodular δ (fun S => f (pre ρ S)) := by
  intro G hG
  set GZ : Finset (Rest ρ) → Oracle ι := fun Z T => G (glue ρ T Z) with hGZdef
  have hGZ : ∀ Z, Submodular (GZ Z) := by
    intro Z T₁ T₂
    simp only [hGZdef]
    rw [← glue_union, ← glue_inter]
    exact hG _ _
  have hcardι : (0 : ℝ) < Fintype.card (Cube ι) := by
    exact_mod_cast Fintype.card_pos
  have hZ : ∀ Z, δ * Fintype.card (Cube ι) ≤ (mismatch f (GZ Z) : ℝ) := by
    intro Z
    have := hf (GZ Z) (hGZ Z)
    unfold distance at this
    rwa [le_div_iff₀ hcardι] at this
  have key : (mismatch (fun S => f (pre ρ S)) G : ℝ) = ∑ Z, (mismatch f (GZ Z) : ℝ) := by
    rw [mismatch_eq_sum]
    rw [← (glueEquiv ρ).sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    rw [mismatch_eq_sum]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    simp [glueEquiv, pre_glue, hGZdef]
  have hcard : (Fintype.card (Cube ι') : ℝ) =
      Fintype.card (Cube ι) * Fintype.card (Finset (Rest ρ)) := by
    rw [← Fintype.card_congr (glueEquiv ρ), Fintype.card_prod]
    push_cast; rfl
  unfold distance
  rw [key, hcard]
  have hpos2 : (0 : ℝ) < Fintype.card (Finset (Rest ρ)) := by exact_mod_cast Fintype.card_pos
  rw [le_div_iff₀ (mul_pos hcardι hpos2)]
  calc δ * (↑(Fintype.card (Cube ι)) * ↑(Fintype.card (Finset (Rest ρ))))
      = ∑ _Z : Finset (Rest ρ), δ * Fintype.card (Cube ι) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ∑ Z, (mismatch f (GZ Z) : ℝ) := Finset.sum_le_sum (fun Z _ => hZ Z)

section Sim
variable {α β : Type}

/-- Rebuild the large-domain history from the small-domain transcript. -/
def lift (A : Procedure β) (h : History α) : History β :=
  h.foldl (fun hN p => match A hN with
    | Sum.inl _ => hN
    | Sum.inr x => hN ++ [(x, p.2)]) []

def sim (A : Procedure β) (P : Cube β → Cube α) : Procedure α := fun h =>
  match A (lift A h) with
  | Sum.inl b => Sum.inl b
  | Sum.inr x => Sum.inr (P x)

lemma lift_snoc (A : Procedure β) (h : History α) (p : Cube α × ℝ) :
    lift A (h ++ [p]) = (match A (lift A h) with
      | Sum.inl _ => lift A h
      | Sum.inr x => lift A h ++ [(x, p.2)]) := by
  simp [lift, List.foldl_append]

lemma run_sim (A : Procedure β) (P : Cube β → Cube α) (f : Oracle α) :
    ∀ (k : ℕ) (h : History α),
      (run (sim A P) f k h).2 = (run A (fun S => f (P S)) k (lift A h)).2 := by
  intro k
  induction k with
  | zero =>
    intro h
    simp only [run, sim]
    cases A (lift A h) <;> rfl
  | succ k ih =>
    intro h
    simp only [run, sim]
    rcases hA : A (lift A h) with b | x
    · rfl
    · simp only
      rw [ih]
      congr 1
      rw [lift_snoc, hA]

lemma accepts_sim (A : Procedure β) (P : Cube β → Cube α) (f : Oracle α) :
    Accepts (sim A P) f ↔ Accepts A (fun S => f (P S)) := by
  unfold Accepts
  simp only [run_sim]
  rfl

lemma budget_sim (A : Procedure β) (P : Cube β → Cube α) (q : ℕ) (hA : Budget A q) :
    Budget (sim A P) q := by
  intro f
  rw [run_sim]
  exact hA _

end Sim


lemma numeric_bound (n m q : ℕ) (hn : 400 ≤ n) (hnm : (n : ℝ) ≤ 2 * ((m : ℝ) + 1) ^ 2 + 3)
    (hq : (q : ℝ) < (2 : ℝ) ^ (Real.sqrt (n : ℝ) / 5)) :
    (q : ℝ) ^ 2 / 2 ^ m + 2 * (q : ℝ) / 2 ^ (2 * m ^ 2 + 2) < 1 / 3 - 2 / 10 := by
  set s := Real.sqrt (n : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = n := Real.sq_sqrt (by positivity)
  have hs20 : 20 ≤ s := by
    rw [hs]; rw [show (20 : ℝ) = Real.sqrt 400 by
      rw [show (400 : ℝ) = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  -- m ≥ 2s/5 + 5
  have hm : 2 * s / 5 + 5 ≤ (m : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : (m : ℝ) + 1 < 2 * s / 5 + 6 := by linarith
    have hm0 : (0 : ℝ) ≤ m + 1 := by positivity
    have h2 : ((m : ℝ) + 1) ^ 2 < (2 * s / 5 + 6) ^ 2 := by
      exact pow_lt_pow_left₀ h1 hm0 (by norm_num)
    nlinarith
  have hm2 : (2 : ℝ) ≤ m := by linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hpow : ∀ x : ℝ, (2 : ℝ) ^ x > 0 := fun x => Real.rpow_pos_of_pos (by norm_num) x
  -- first term
  have hA : (q : ℝ) ^ 2 < (2 : ℝ) ^ ((m : ℝ) - 5) := by
    have h1 : (q : ℝ) ^ 2 < ((2 : ℝ) ^ (s / 5)) ^ 2 := pow_lt_pow_left₀ hq hq0 (by norm_num)
    have h2 : ((2 : ℝ) ^ (s / 5)) ^ 2 = (2 : ℝ) ^ (2 * s / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    have h3 : (2 : ℝ) ^ (2 * s / 5) ≤ (2 : ℝ) ^ ((m : ℝ) - 5) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have hA' : (2 : ℝ) ^ ((m : ℝ) - 5) = (2 : ℝ) ^ m / 32 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]; norm_num
  have hT1 : (q : ℝ) ^ 2 / 2 ^ m < 1 / 32 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  -- second term
  have hB : (q : ℝ) < 2 ^ m := by
    have : (2 : ℝ) ^ (s / 5) ≤ (2 : ℝ) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_natCast] at this; linarith
  have hmN : m + 6 ≤ 2 * m ^ 2 + 2 := by
    have : 2 ≤ m := by exact_mod_cast hm2
    nlinarith
  have hB2 : (2 : ℝ) ^ (m + 6) ≤ 2 ^ (2 * m ^ 2 + 2) := pow_le_pow_right₀ (by norm_num) hmN
  have hT2 : 2 * (q : ℝ) / 2 ^ (2 * m ^ 2 + 2) < 1 / 32 := by
    rw [div_lt_iff₀ (by positivity)]
    have : (2 : ℝ) ^ (m + 6) = 2 ^ m * 64 := by rw [pow_add]; norm_num
    nlinarith
  linarith

/-- Discrete sample type for the hard distributions. -/
def Xi (m : ℕ) : Type := Sample m

noncomputable instance (m : ℕ) : Fintype (Xi m) := inferInstanceAs (Fintype (Sample m))
noncomputable instance (m : ℕ) : DecidableEq (Xi m) := Classical.decEq _
instance (m : ℕ) : Nonempty (Xi m) :=
  ⟨((fun _ _ => false), (fun _ _ => false), (fun _ => ⟨0, by positivity⟩))⟩
instance (m : ℕ) : MeasurableSpace (Xi m) := ⊤

open Classical in
lemma real_uniform_eq {m : ℕ} (p : Xi m → Prop) :
    (PMF.uniformOfFintype (Xi m)).toMeasure.real {ξ | p ξ} =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card (Xi m) := by
  classical
  rw [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ MeasurableSpace.measurableSet_top]
  rw [ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  congr 1
  rw [Fintype.card_subtype]
  congr 3

open Classical in
lemma uniformProb_eq_xi {m : ℕ} (p : Sample m → Prop) :
    uniformProb p = ((Finset.univ.filter (fun ξ : Xi m => p ξ)).card : ℝ) / Fintype.card (Xi m) := by
  classical
  unfold uniformProb
  congr 2

end BTMain

open BTMain in
theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < (1/10^8 : ℝ)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (T : Tester (Fin n) Ω) (q : ℕ),
        Correct μ T Submodular ε → TesterBudget T q →
          (2 : ℝ) ^ (Real.sqrt (n : ℝ) / 5) ≤ (q : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := soundness
  refine ⟨max 400 (2 * (M + 9) ^ 2 + 3), ?_⟩
  intro n hn Ω _ μ _ T q hcorr hbud
  by_contra hlt
  push Not at hlt
  have hn400 : 400 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : 2 * (M + 9) ^ 2 + 3 ≤ n := le_trans (le_max_right _ _) hn
  set k := (n - 2) / 2 with hk
  set m := Nat.sqrt k with hmdef
  have hmk : m ^ 2 ≤ k := Nat.sqrt_le' k
  have hkm : k < (m + 1) * (m + 1) := Nat.lt_succ_sqrt k
  have h2k : 2 * k ≤ n - 2 := Nat.mul_div_le (n - 2) 2
  have hk2 : n - 2 < 2 * k + 2 := by omega
  have hdim : dimension m ≤ n := by unfold dimension; omega
  have hMm : M + 9 ≤ m := by
    rw [hmdef, Nat.le_sqrt]
    rw [sq] at hnM
    generalize (M + 9) * (M + 9) = t at hnM ⊢
    omega
  have hm9 : 9 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  have hnreal : (n : ℝ) ≤ 2 * ((m : ℝ) + 1) ^ 2 + 3 := by
    have : n ≤ 2 * ((m + 1) * (m + 1)) + 3 := by omega
    have : (n : ℝ) ≤ 2 * (((m : ℝ) + 1) * ((m : ℝ) + 1)) + 3 := by exact_mod_cast this
    nlinarith
  have hnum := numeric_bound n m q hn400 hnreal hlt
  -- coordinate embedding
  let ρ : Coord m ↪ Fin n := (coordEquiv m).toEmbedding.trans (Fin.castLEEmb hdim)
  let Fyes : Xi m → Oracle (Fin n) := fun ξ S => hard (ξ : Sample m) true (pre ρ S)
  let Fno : Xi m → Oracle (Fin n) := fun ξ S => hard (ξ : Sample m) false (pre ρ S)
  let D : Measure (Xi m) := (PMF.uniformOfFintype (Xi m)).toMeasure
  have hyes : ∀ ξ, Submodular (Fyes ξ) := fun ξ =>
    submodular_comp_pre ρ _ (completeness hm9 (ξ : Sample m))
  have hno : 1 - 2 / 10 ≤ D.real {ξ | Far Submodular ε (Fno ξ)} := by
    have h1 := hM m (by omega)
    rw [uniformProb_eq_xi] at h1
    rw [show D = (PMF.uniformOfFintype (Xi m)).toMeasure from rfl, real_uniform_eq]
    have hsub : (Finset.univ.filter (fun ξ : Xi m => Far Submodular (1/10^8 : ℝ) (hard ξ false))).card
        ≤ (Finset.univ.filter (fun ξ : Xi m => Far Submodular ε (Fno ξ))).card := by
      apply Finset.card_le_card
      intro ξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hξ
      have h2 := far_comp_pre ρ _ _ hξ
      intro G hG
      exact le_trans (by linarith) (h2 G hG)
    have hcpos : (0 : ℝ) < Fintype.card (Xi m) := by exact_mod_cast Fintype.card_pos
    have : ((Finset.univ.filter (fun ξ : Xi m => Far Submodular (1/10^8 : ℝ) (hard ξ false))).card : ℝ)
        / Fintype.card (Xi m) ≤
        ((Finset.univ.filter (fun ξ : Xi m => Far Submodular ε (Fno ξ))).card : ℝ) / Fintype.card (Xi m) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsub) hcpos.le
    linarith
  have hgap : ∀ A : Procedure (Fin n), Budget A q →
      MeasurableSet {ξ | Accepts A (Fyes ξ)} → MeasurableSet {ξ | Accepts A (Fno ξ)} →
        |D.real {ξ | Accepts A (Fyes ξ)} - D.real {ξ | Accepts A (Fno ξ)}| < 1/3 - 2/10 := by
    intro A hA _ _
    have hB := indistinguishability hm1 (sim A (pre ρ)) q (budget_sim A (pre ρ) q hA)
    have e1 : D.real {ξ | Accepts A (Fyes ξ)} = acceptanceProbability (sim A (pre ρ)) true := by
      have hset : {ξ | Accepts A (Fyes ξ)} = {ξ : Xi m | Accepts (sim A (pre ρ)) (hard ξ true)} := by
        ext ξ; exact (accepts_sim _ _ _).symm
      rw [hset, show D = (PMF.uniformOfFintype (Xi m)).toMeasure from rfl, real_uniform_eq]; unfold acceptanceProbability; rw [uniformProb_eq_xi]
    have e2 : D.real {ξ | Accepts A (Fno ξ)} = acceptanceProbability (sim A (pre ρ)) false := by
      have hset : {ξ | Accepts A (Fno ξ)} = {ξ : Xi m | Accepts (sim A (pre ρ)) (hard ξ false)} := by
        ext ξ; exact (accepts_sim _ _ _).symm
      rw [hset, show D = (PMF.uniformOfFintype (Xi m)).toMeasure from rfl, real_uniform_eq]; unfold acceptanceProbability; rw [uniformProb_eq_xi]
    rw [e1, e2]
    unfold dimension at hB
    linarith
  have hjoint : ∀ F : Xi m → Oracle (Fin n),
      MeasurableSet {p : Ω × Xi m | Accepts (T.procedure p.1) (F p.2)} := by
    intro F
    have : {p : Ω × Xi m | Accepts (T.procedure p.1) (F p.2)} =
        ⋃ ξ : Xi m, {ω | Accepts (T.procedure ω) (F ξ)} ×ˢ {ξ} := by
      ext ⟨ω, ξ⟩
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
      constructor
      · intro h; exact ⟨ξ, h, rfl⟩
      · rintro ⟨ξ', h, rfl⟩; exact h
    rw [this]
    exact MeasurableSet.iUnion (fun ξ =>
      (T.accept_measurable (F ξ)).prod MeasurableSpace.measurableSet_top)
  exact yao Submodular ε (2/10) ⟨hε0, by linarith⟩ ⟨by norm_num, by norm_num⟩ q D D Fyes Fno
    (fun _ => measurable_from_top) (fun _ => measurable_from_top) hyes
    MeasurableSpace.measurableSet_top hno hgap μ T (hjoint Fyes) (hjoint Fno) hcorr hbud
