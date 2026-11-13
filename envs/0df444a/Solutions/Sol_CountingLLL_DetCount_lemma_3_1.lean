-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:06:31.228611+00:00
-- url     : https://prove2.me/submissions/547b3c5b-0b11-42a4-b1dd-b5c598306299

import Theorems.Thm_CountingLLL_DetCount_theorem_2_2
import Theorems.Thm_CountingLLL_DetCount_condition11_partition_positive

set_option autoImplicit false
open CountingLLL.DetCount CountingLLL.DetCount.CSP
open scoped Classical

private theorem p_nonneg (Φ : CSP) : 0 ≤ Φ.pmax := by
  unfold CSP.pmax
  exact NNReal.coe_nonneg _

private theorem p_bad (Φ : CSP) (c : Fin Φ.m) : Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ Φ.pmax := by
  classical
  have h : Φ.violProb c ≤ Finset.univ.sup Φ.violProb := Finset.le_sup (Finset.mem_univ c)
  have hr : ((Φ.violProb c : NNReal) : ℝ) ≤ ((Finset.univ.sup Φ.violProb : NNReal) : ℝ) := by exact_mod_cast h
  have heq : Φ.prob (fun σ => ¬ Φ.Sat c σ) = (Φ.violProb c : ℝ) := by
    unfold CSP.prob CSP.violProb
    push_cast
    congr 1
    congr 1
    apply congrArg Finset.card
    exact Finset.filter_congr_decidable Finset.univ (fun σ : Φ.Config => ¬ Φ.Sat c σ) (fun σ => Classical.propDecidable _)
  rw [heq]
  exact hr

private theorem numeric_lll (p D : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (h : 4 * Real.exp 1 * p * (D+1)^2 ≤ 1) :
    0 ≤ 6*p/5 ∧ 6*p/5 < 1 ∧ 6*p/5*D ≤ 1/10 := by
  have he : 2 < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have hd4 : 0 ≤ p * ((D+1)^2 - 4*D) := by
    have hs : 0 ≤ (D-1)^2 := sq_nonneg _
    have : 0 ≤ (D+1)^2 - 4*D := by nlinarith
    exact mul_nonneg hp this
  have hegap : 0 ≤ 4 * p * (Real.exp 1 - 2) * (D+1)^2 := by positivity
  have hs : 0 ≤ p * ((D+1)^2 - 1) := by
    have : 0 ≤ (D+1)^2 - 1 := by nlinarith [sq_nonneg D]
    exact mul_nonneg hp this
  constructor
  · positivity
  constructor
  · nlinarith
  · nlinarith

private theorem degree_subfamily (Φ : CSP) (E : Finset (Fin Φ.m)) (c : Fin Φ.m) :
    (Φ.nbr E c).card ≤ Φ.Dmax := by
  classical
  have hsub : Φ.nbr E c ⊆ Φ.nbr Finset.univ c := by
    intro j hj
    simp only [CSP.nbr, Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, hj.2⟩
  apply le_trans (Finset.card_le_card hsub)
  unfold CSP.Dmax CSP.Dsub
  exact Finset.le_sup (f := fun j => (Φ.nbr Finset.univ j).card) (Finset.mem_univ c)

private theorem base_power (p : ℝ) (D : ℕ) (hp : 0 ≤ p) (hx : 6*p/5 < 1)
    (hsmall : 6*p/5 * (D : ℝ) ≤ 1/10) :
    (9/10 : ℝ) ≤ (1 - 6*p/5)^D := by
  have hbern := one_add_mul_le_pow (a := -(6*p/5)) (by linarith : (-2:ℝ) ≤ -(6*p/5)) D
  have hbern' : 1 + (D:ℝ)*(-(6*p/5)) ≤ (1 - 6*p/5)^D := by simpa only [sub_eq_add_neg] using hbern
  nlinarith

private theorem local_condition (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m))
    (c : Fin Φ.m) :
    Φ.prob (fun σ => ¬ Φ.Sat c σ) ≤ (6*Φ.pmax/5) *
      ∏ j ∈ Φ.nbr E c, (1 - 6*Φ.pmax/5) := by
  have hp := p_nonneg Φ
  have hd : (0:ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hn := numeric_lll Φ.pmax (Φ.Dmax : ℝ) hp hd hΦ
  have hb : (0:ℝ) ≤ 1 - 6*Φ.pmax/5 := by linarith [hn.2.1]
  have hb1 : (1:ℝ) - 6*Φ.pmax/5 ≤ 1 := by linarith [hn.1]
  have hpow := base_power Φ.pmax Φ.Dmax hp hn.2.1 hn.2.2
  have hdeg := degree_subfamily Φ E c
  have hpow' : (1 - 6*Φ.pmax/5)^Φ.Dmax ≤
      (1 - 6*Φ.pmax/5)^(Φ.nbr E c).card :=
    pow_le_pow_of_le_one hb hb1 hdeg
  have hprod : (9/10:ℝ) ≤ ∏ j ∈ Φ.nbr E c, (1 - 6*Φ.pmax/5) := by
    simpa only [Finset.prod_const] using hpow.trans hpow'
  have hpbound := p_bad Φ c
  have hmul := mul_le_mul_of_nonneg_left hprod hn.1
  nlinarith

private theorem prob_as_indicator (Φ : CSP) (A : Φ.Config → Prop) :
    Φ.prob A = (∑ σ : Φ.Config, if A σ then (1 : ℝ) else 0) / Fintype.card Φ.Config := by
  classical
  unfold CSP.prob
  congr 1
  simp [Finset.sum_ite]


private theorem satall_decompose (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (σ : Φ.Config) :
    Φ.SatAll E σ ↔ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ := by
  classical
  constructor
  · intro h
    exact ⟨h r hr, fun c hc => h c (Finset.mem_of_mem_erase hc)⟩
  · rintro ⟨hrsat, hrest⟩ c hc
    by_cases hcr : c = r
    · subst c; exact hrsat
    · exact hrest c (Finset.mem_erase.mpr ⟨hcr, hc⟩)

private theorem probability_partition (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) :
    Φ.prob (Φ.SatAll E) + Φ.prob (fun σ => ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) =
      Φ.prob (Φ.SatAll (E.erase r)) := by
  classical
  simp only [prob_as_indicator, ← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  have h := satall_decompose Φ E r hr σ
  by_cases h1 : Φ.Sat r σ <;> by_cases h2 : Φ.SatAll (E.erase r) σ <;> simp [h1, h2, h]

private theorem card_config_nonzero (Φ : CSP) : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))

private theorem prob_satall (Φ : CSP) (E : Finset (Fin Φ.m)) :
    Φ.prob (Φ.SatAll E) = (Φ.Z E : ℝ) / Fintype.card Φ.Config := by rfl

private theorem prob_satall_ne_zero (Φ : CSP) (E : Finset (Fin Φ.m)) (h : 0 < Φ.Z E) :
    Φ.prob (Φ.SatAll E) ≠ 0 := by
  rw [prob_satall]
  apply div_ne_zero
  · exact_mod_cast (ne_of_gt h)
  · exact card_config_nonzero Φ


private theorem prob_nonneg (Φ : CSP) (A : Φ.Config → Prop) : 0 ≤ Φ.prob A := by
  rw [prob_as_indicator]
  positivity

private theorem prob_mono (Φ : CSP) (A B : Φ.Config → Prop) (h : ∀ σ, A σ → B σ) : Φ.prob A ≤ Φ.prob B := by
  classical
  rw [prob_as_indicator, prob_as_indicator]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro σ hσ
  by_cases ha : A σ
  · have hb := h σ ha
    simp [ha, hb]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> norm_num

private theorem r_eq_cond (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c : Fin Φ.m) (hc : c ∈ E) :
    Φ.r E c = Φ.condProb (fun σ => ¬ Φ.Sat c σ) (Φ.SatAll (E.erase c)) := by
  have hz := CountingLLL.DetCount.condition11_partition_positive Φ hΦ (E.erase c)
  have hn := prob_satall_ne_zero Φ (E.erase c) hz
  have hp := probability_partition Φ E c hc
  have hr : Φ.prob (Φ.SatAll E) / Φ.prob (Φ.SatAll (E.erase c)) =
      (Φ.Z E : ℝ) / (Φ.Z (E.erase c) : ℝ) := by
    rw [prob_satall, prob_satall]
    exact div_div_div_cancel_right₀ (card_config_nonzero Φ) _ _
  unfold CSP.r CSP.condProb
  rw [← hr]
  field_simp
  linarith

private theorem upper_of_conditional_lll (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (c : Fin Φ.m) (hc : c ∈ E) (hp : 0 < Φ.pmax) :
    Φ.condProb (fun σ => ¬ Φ.Sat c σ) (Φ.SatAll (E.erase c)) ≤ 6*Φ.pmax/5 := by
  classical
  let x : Fin Φ.m → ℝ := fun _ => 6*Φ.pmax/5
  let F := E.erase c
  have hp0 := p_nonneg Φ
  have hn := numeric_lll Φ.pmax (Φ.Dmax : ℝ) hp0 (Nat.cast_nonneg _) hΦ
  have hx : ∀ j ∈ F, 0 < x j ∧ x j < 1 := by
    intro j hj
    dsimp [x]
    constructor <;> nlinarith [hn.2.1]
  have h6 : ∀ j ∈ F, Φ.prob (fun σ => ¬ Φ.Sat j σ) ≤
      x j * ∏ j' ∈ Φ.nbr F j, (1 - x j') := by
    intro j hj
    simpa [x] using local_condition Φ hΦ F j
  have hA : ∀ σ σ' : Φ.Config, (∀ v ∈ Φ.scope c, σ v = σ' v) →
      ((¬ Φ.Sat c σ) ↔ (¬ Φ.Sat c σ')) := by
    intro σ σ' h
    have hrestrict : (fun v : ↥(Φ.scope c) => σ v.1) = (fun v : ↥(Φ.scope c) => σ' v.1) := by
      funext v
      exact h v.1 v.2
    simp only [CSP.Sat, hrestrict]
  have hcond := CountingLLL.DetCount.theorem_2_2 Φ F x hx h6
    (fun σ => ¬ Φ.Sat c σ) (Φ.scope c) hA
  have hnbr : F.filter (fun j => ¬ Disjoint (Φ.scope j) (Φ.scope c)) = Φ.nbr E c := by
    ext j
    change j ∈ (E.erase c).filter (fun j => ¬ Disjoint (Φ.scope j) (Φ.scope c)) ↔ j ∈ Φ.nbr E c
    unfold CSP.nbr
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
    simp only [CSP.Overlap, disjoint_comm]
    tauto
  rw [hnbr] at hcond
  have hbase : (0:ℝ) < 1 - 6*Φ.pmax/5 := by linarith [hn.2.1]
  have hbase1 : 1 - 6*Φ.pmax/5 ≤ 1 := by linarith [hn.1]
  have hdeg := degree_subfamily Φ E c
  have hpow := base_power Φ.pmax Φ.Dmax hp0 hn.2.1 hn.2.2
  have hpow' : (1 - 6*Φ.pmax/5)^Φ.Dmax ≤
      (1 - 6*Φ.pmax/5)^(Φ.nbr E c).card :=
    pow_le_pow_of_le_one hbase.le hbase1 hdeg
  have htarget : (9/10:ℝ) ≤ (1 - 6*Φ.pmax/5)^(Φ.nbr E c).card := hpow.trans hpow'
  have hInv : ((1 - 6*Φ.pmax/5)^(Φ.nbr E c).card)⁻¹ ≤ 10/9 := by
    apply (inv_le_iff_one_le_mul₀ (pow_pos hbase _)).2
    nlinarith
  have hmul := mul_le_mul (p_bad Φ c) hInv (inv_nonneg.mpr (pow_nonneg hbase.le _)) hp0
  have hbound : Φ.prob (fun σ => ¬ Φ.Sat c σ) *
      ∏ j ∈ Φ.nbr E c, (1 - x j)⁻¹ ≤ Φ.pmax * (10/9) := by
    simpa [x, Finset.prod_const, ← Finset.prod_inv_distrib] using hmul
  exact hcond.trans (by nlinarith [hbound])

theorem solution (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) : 0 ≤ Φ.r E c₀ ∧ Φ.r E c₀ ≤ 1.2 * Φ.pmax := by
  have heq := r_eq_cond Φ hΦ E c₀ hc₀
  rw [heq]
  constructor
  · unfold CSP.condProb
    exact div_nonneg (prob_nonneg Φ _) (prob_nonneg Φ _)
  · by_cases hp : Φ.pmax = 0
    · have hbad0 : Φ.prob (fun σ => ¬ Φ.Sat c₀ σ) = 0 := by
        apply le_antisymm
        · simpa [hp] using p_bad Φ c₀
        · exact prob_nonneg Φ _
      have hnum0 : Φ.prob (fun σ => ¬ Φ.Sat c₀ σ ∧ Φ.SatAll (E.erase c₀) σ) = 0 := by
        apply le_antisymm
        · calc
            _ ≤ Φ.prob (fun σ => ¬ Φ.Sat c₀ σ) := prob_mono Φ _ _ (fun _ h => h.1)
            _ = 0 := hbad0
        · exact prob_nonneg Φ _
      simp [CSP.condProb, hnum0, hp]
    · have hp' : 0 < Φ.pmax := lt_of_le_of_ne (p_nonneg Φ) (Ne.symm hp)
      have hh := upper_of_conditional_lll Φ hΦ E c₀ hc₀ hp'
      nlinarith
