-- Prove2me | solution 1 for G2GImport.Sourcing.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:08:56.062966+00:00
-- url     : https://prove2.me/submissions/7c1bc44b-187f-4d11-a5b9-cb674a364760

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model
import Definitions.Def_G2GImport_Sourcing_ClosedForms


namespace G2GImport.Sourcing

noncomputable def kap (γ : ℝ) : ℝ := γ ^ γ * (1 - γ) ^ (1 - γ)

lemma kap_pos {γ : ℝ} (h0 : 0 < γ) (h1 : γ < 1) : 0 < kap γ := by
  unfold kap
  have : 0 < 1 - γ := by linarith
  positivity

/-- weighted AM-GM in Nash-product form -/
lemma nash_le {γ a b : ℝ} (h0 : 0 < γ) (h1 : γ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    nashProd γ a b ≤ kap γ * (a + b) := by
  have h1' : 0 < 1 - γ := by linarith
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := γ) (w₂ := 1 - γ)
    (p₁ := a / γ) (p₂ := b / (1 - γ)) h0.le h1'.le (by positivity) (by positivity) (by ring)
  rw [Real.div_rpow ha h0.le, Real.div_rpow hb h1'.le] at key
  have e1 : γ * (a / γ) + (1 - γ) * (b / (1 - γ)) = a + b := by field_simp
  rw [e1] at key
  have hk := kap_pos h0 h1
  unfold nashProd
  unfold kap at hk ⊢
  have hg : 0 < γ ^ γ := by positivity
  have hg' : 0 < (1 - γ) ^ (1 - γ) := by positivity
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)] at key
  linarith [key]

lemma nash_eq_imp {γ a b : ℝ} (h0 : 0 < γ) (h1 : γ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heq : kap γ * (a + b) ≤ nashProd γ a b) : b = (1 - γ) * (a + b) := by
  have h1' : 0 < 1 - γ := by linarith
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := γ) (w₂ := 1 - γ)
    (p₁ := a / γ) (p₂ := b / (1 - γ)) h0.le h1'.le (by positivity) (by positivity) (by ring)
  have iff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos (w₁ := γ) (w₂ := 1 - γ)
    (p₁ := a / γ) (p₂ := b / (1 - γ)) h0 h1' (by positivity) (by positivity) (by ring)
  have e1 : γ * (a / γ) + (1 - γ) * (b / (1 - γ)) = a + b := by field_simp
  rw [e1] at key iff
  have hg : 0 < γ ^ γ := by positivity
  have hg' : 0 < (1 - γ) ^ (1 - γ) := by positivity
  have hdiv : (a / γ) ^ γ * (b / (1 - γ)) ^ (1 - γ) = nashProd γ a b / kap γ := by
    unfold nashProd kap
    rw [Real.div_rpow ha h0.le, Real.div_rpow hb h1'.le, div_mul_div_comm]
  have hk := kap_pos h0 h1
  have : (a / γ) ^ γ * (b / (1 - γ)) ^ (1 - γ) = a + b := by
    apply le_antisymm key
    rw [hdiv, le_div_iff₀ hk]; linarith
  have h2 := iff.mp this
  field_simp at h2
  linarith

lemma nash_at {γ S : ℝ} (h0 : 0 < γ) (h1 : γ < 1) (hS : 0 ≤ S) :
    nashProd γ (γ * S) ((1 - γ) * S) = kap γ * S := by
  have h1' : 0 < 1 - γ := by linarith
  unfold nashProd kap
  rw [Real.mul_rpow h0.le hS, Real.mul_rpow h1'.le hS]
  have : S ^ γ * S ^ (1 - γ) = S := by
    rw [← Real.rpow_add' hS (by norm_num)]; simp
  calc γ ^ γ * S ^ γ * ((1 - γ) ^ (1 - γ) * S ^ (1 - γ))
      = γ ^ γ * (1 - γ) ^ (1 - γ) * (S ^ γ * S ^ (1 - γ)) := by ring
    _ = _ := by rw [this]

/-- Necessity for a generic NBS whose buyer gain is `V q - t` and supplier gain `t - C q`. -/
lemma nbs_nec {γ : ℝ} (h0 : 0 < γ) (h1 : γ < 1) {A : Set ℝ} {gB gS : ℝ → ℝ → ℝ}
    {V C : ℝ → ℝ} (hB : ∀ q t, gB q t = V q - t) (hS : ∀ q t, gS q t = t - C q)
    (hC : ∀ q ∈ A, 0 ≤ C q) {q t : ℝ} (h : IsNBS γ A gB gS q t) :
    q ∈ A ∧ 0 ≤ V q - C q ∧ (∀ q' ∈ A, V q' - C q' ≤ V q - C q) ∧
      (0 < V q - C q → t = C q + (1 - γ) * (V q - C q)) := by
  obtain ⟨hq, ht, hb, hs, hmax⟩ := h
  rw [hB] at hb; rw [hS] at hs
  have hk := kap_pos h0 h1
  have hup : nashProd γ (gB q t) (gS q t) ≤ kap γ * (V q - C q) := by
    rw [hB, hS]
    have := nash_le h0 h1 hb hs
    convert this using 2; ring
  refine ⟨hq, by linarith, ?_, ?_⟩
  · intro q' hq'
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < V q' - C q' := by linarith
    have hm := hmax q' hq' (C q' + (1 - γ) * (V q' - C q'))
      (by have := hC q' hq'; nlinarith) (by rw [hB]; nlinarith) (by rw [hS]; nlinarith)
    simp only [hB, hS] at hm hup
    have e1 : V q' - (C q' + (1 - γ) * (V q' - C q')) = γ * (V q' - C q') := by ring
    have e2 : C q' + (1 - γ) * (V q' - C q') - C q' = (1 - γ) * (V q' - C q') := by ring
    rw [e1, e2, nash_at h0 h1 hpos.le] at hm
    have := mul_lt_mul_of_pos_left hlt hk
    linarith
  · intro hpos
    have hm := hmax q hq (C q + (1 - γ) * (V q - C q))
      (by have := hC q hq; nlinarith) (by rw [hB]; nlinarith) (by rw [hS]; nlinarith)
    simp only [hB, hS] at hm
    have e1 : V q - (C q + (1 - γ) * (V q - C q)) = γ * (V q - C q) := by ring
    have e2 : C q + (1 - γ) * (V q - C q) - C q = (1 - γ) * (V q - C q) := by ring
    rw [e1, e2, nash_at h0 h1 hpos.le] at hm
    have := nash_eq_imp h0 h1 hb hs (by convert hm using 2; ring)
    have e3 : V q - t + (t - C q) = V q - C q := by ring
    rw [e3] at this
    linarith

lemma nbs_suff {γ : ℝ} (h0 : 0 < γ) (h1 : γ < 1) {A : Set ℝ} {gB gS : ℝ → ℝ → ℝ}
    {V C : ℝ → ℝ} (hB : ∀ q t, gB q t = V q - t) (hS : ∀ q t, gS q t = t - C q)
    {q t : ℝ} (hq : q ∈ A) (hCq : 0 ≤ C q) (hpos : 0 ≤ V q - C q)
    (hmax : ∀ q' ∈ A, V q' - C q' ≤ V q - C q)
    (ht : t = C q + (1 - γ) * (V q - C q)) : IsNBS γ A gB gS q t := by
  have hk := kap_pos h0 h1
  have e1 : V q - t = γ * (V q - C q) := by rw [ht]; ring
  have e2 : t - C q = (1 - γ) * (V q - C q) := by rw [ht]; ring
  refine ⟨hq, by rw [ht]; nlinarith, by rw [hB, e1]; positivity, by rw [hS, e2]; nlinarith, ?_⟩
  intro q' hq' t' _ hb hs
  simp only [hB, hS] at hb hs ⊢
  rw [e1, e2, nash_at h0 h1 hpos]
  have := nash_le h0 h1 hb hs
  have e3 : V q' - t' + (t' - C q') = V q' - C q' := by ring
  rw [e3] at this
  have := mul_le_mul_of_nonneg_left (hmax q' hq') hk.le
  linarith

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma g_def (x : ℝ) : supplyUtil x = 2 * min 1 x - (min 1 x) ^ 2 := rfl

lemma g_cont : Continuous supplyUtil := by
  have : supplyUtil = fun x => 2 * min 1 x - (min 1 x) ^ 2 := rfl
  rw [this]; fun_prop

lemma g_le1 {x : ℝ} (h : x ≤ 1) : supplyUtil x = 2 * x - x ^ 2 := by
  rw [g_def, min_eq_right h]

lemma g_ge1 {x : ℝ} (h : 1 ≤ x) : supplyUtil x = 1 := by
  rw [g_def, min_eq_left h]; ring

lemma g_tangent (x x' : ℝ) :
    supplyUtil x' ≤ supplyUtil x + 2 * max 0 (1 - x) * (x' - x) := by
  rcases le_total x 1 with hx | hx
  · rw [g_le1 hx, max_eq_right (by linarith)]
    rcases le_total x' 1 with hx' | hx'
    · rw [g_le1 hx']; nlinarith [sq_nonneg (x' - x)]
    · rw [g_ge1 hx']; nlinarith
  · rw [g_ge1 hx, max_eq_left (by linarith), g_def]
    nlinarith [sq_nonneg (min 1 x' - 1)]

lemma g_mono {x x' : ℝ} (h : x ≤ x') : supplyUtil x ≤ supplyUtil x' := by
  rcases le_total x' 1 with hx' | hx'
  · rw [g_le1 hx', g_le1 (by linarith)]; nlinarith
  · rw [g_ge1 hx', g_def]; nlinarith [sq_nonneg (min 1 x - 1)]

lemma g_strict {x x' : ℝ} (h : x < x') (h1 : x < 1) : supplyUtil x < supplyUtil x' := by
  rw [g_le1 h1.le]
  rcases le_total x' 1 with hx' | hx'
  · rw [g_le1 hx']; nlinarith
  · rw [g_ge1 hx']; nlinarith [sq_nonneg (x - 1)]

lemma g_min1 (x : ℝ) : supplyUtil (min x 1) = supplyUtil x := by
  simp only [g_def]
  rw [min_comm x 1, ← min_assoc, min_self]

lemma int_quad (p q r a b : ℝ) :
    ∫ x in a..b, (p + q * x + r * x ^ 2) =
      p * (b - a) + q * (b ^ 2 - a ^ 2) / 2 + r * (b ^ 3 - a ^ 3) / 3 := by
  have hF : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => p * x + q * x ^ 2 / 2 + r * x ^ 3 / 3)
      (p + q * x + r * x ^ 2) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul p).add (((hasDerivAt_pow 2 x).const_mul q).div_const 2)).add
      (((hasDerivAt_pow 3 x).const_mul r).div_const 3)
    exact this.congr_deriv (by norm_num; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- split `[0,1]` at `m` and replace the integrand on each piece -/
lemma int_split {f f1 f2 : ℝ → ℝ} (hf : Continuous f) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (h1 : ∀ y, 0 ≤ y → y ≤ m → f y = f1 y) (h2 : ∀ y, m ≤ y → y ≤ 1 → f y = f2 y) :
    ∫ y in (0 : ℝ)..1, f y = (∫ y in (0 : ℝ)..m, f1 y) + ∫ y in m..1, f2 y := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hm0] at hy
    exact h1 y hy.1 hy.2
  · apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hm1] at hy
    exact h2 y hy.1 hy.2

noncomputable def Wf (a : ℝ) : ℝ := EY (fun y => supplyUtil (y + a))
noncomputable def Df (a : ℝ) : ℝ := ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - y - a)

lemma W_formula {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : Wf a = 1 - (1 - a) ^ 3 / 3 := by
  unfold Wf EY
  rw [int_split (f1 := fun y => (2 * a - a ^ 2) + (2 - 2 * a) * y + (-1) * y ^ 2)
    (f2 := fun y => 1 + 0 * y + 0 * y ^ 2) (f := fun y => supplyUtil (y + a))
    (g_cont.comp (continuous_id.add continuous_const))
    (m := 1 - a) (by linarith) (by linarith)]
  · rw [int_quad, int_quad]; ring
  · intro y _ hy; rw [g_le1 (by linarith)]; ring
  · intro y hy _; rw [g_ge1 (by linarith)]; ring

lemma D_formula {a : ℝ} (h0 : 0 ≤ a) : Df a = (max 0 (1 - a)) ^ 2 := by
  unfold Df
  rcases le_total a 1 with h1 | h1
  · rw [int_split (f1 := fun y => (2 - 2 * a) + (-2) * y + 0 * y ^ 2)
      (f2 := fun y => 0 + 0 * y + 0 * y ^ 2) (f := fun y => 2 * max 0 (1 - y - a)) (by fun_prop)
      (m := 1 - a) (by linarith) (by linarith)]
    · rw [int_quad, int_quad, max_eq_right (by linarith)]; ring
    · intro y _ hy; rw [max_eq_right (by linarith)]; ring
    · intro y hy _; rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith)]
    have : ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - y - a) = ∫ y in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      simp only
      rw [max_eq_left (by linarith [hy.1])]; ring
    rw [this]; simp

lemma W_tangent (a b : ℝ) : Wf b ≤ Wf a + (b - a) * Df a := by
  unfold Wf Df EY
  have c1 : Continuous (fun y => supplyUtil (y + a)) := g_cont.comp (continuous_id.add continuous_const)
  have c2 : Continuous (fun y => supplyUtil (y + b)) := g_cont.comp (continuous_id.add continuous_const)
  have c3 : Continuous (fun y : ℝ => (b - a) * (2 * max 0 (1 - y - a))) := by fun_prop
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c3.intervalIntegrable _ _)]
  apply intervalIntegral.integral_mono_on (by norm_num) (c2.intervalIntegrable _ _)
    ((c1.add c3).intervalIntegrable _ _)
  intro y _
  have := g_tangent (y + a) (y + b)
  have e : 1 - (y + a) = 1 - y - a := by ring
  rw [e] at this
  simp only [Pi.add_apply]
  nlinarith [this]

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma EY_shift (X q' : ℝ) :
    EY (fun y => supplyUtil (y + X + q')) = Wf (X + q') := by
  unfold Wf; congr 1; funext y; ring_nf

lemma sqrt_facts (P : Params) (hS : P.Standing) :
    0 < Real.sqrt P.c ∧ Real.sqrt P.c < 1 ∧ Real.sqrt P.c ^ 2 = P.c := by
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS
  have h2 : Real.sqrt P.c ^ 2 = P.c := Real.sq_sqrt hc0.le
  have h0 : 0 < Real.sqrt P.c := Real.sqrt_pos.mpr hc0
  refine ⟨h0, ?_, h2⟩
  nlinarith

/-- surplus of the forward bargain at the symmetric quantity -/
lemma fwd_surplus (P : Params) (hS : P.Standing) (L : ℝ) (hL : 1 ≤ L) :
    Wf ((L - 1) * ((1 - Real.sqrt P.c) / L) + (1 - Real.sqrt P.c) / L)
      - Wf ((L - 1) * ((1 - Real.sqrt P.c) / L)) - P.c * ((1 - Real.sqrt P.c) / L) =
      Real.sqrt P.c * ((1 - Real.sqrt P.c) / L) ^ 2 + ((1 - Real.sqrt P.c) / L) ^ 3 / 3 := by
  obtain ⟨h0, h1, h2⟩ := sqrt_facts P hS
  set s := Real.sqrt P.c
  set q := (1 - s) / L with hq
  have hLpos : 0 < L := by linarith
  have hq0 : 0 ≤ q := by positivity
  have hQ : (L - 1) * q + q = 1 - s := by rw [hq]; field_simp; ring
  have hX0 : 0 ≤ (L - 1) * q := mul_nonneg (by linarith) hq0
  rw [hQ, W_formula (by linarith) (by linarith), W_formula hX0 (by linarith)]
  have hX : (L - 1) * q = 1 - s - q := by linarith
  rw [hX, ← h2]; ring

theorem fwd_char (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (q t : ℝ) :
    IsForwardEq P l q t ↔
      q = (1 - Real.sqrt P.c) / (l : ℝ) ∧
      t = P.c * q + (1 - P.γ) * (Real.sqrt P.c * q ^ 2 + q ^ 3 / 3) := by
  obtain ⟨h0, h1, h2⟩ := sqrt_facts P hS
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  set s := Real.sqrt P.c with hs
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hB : ∀ q' t', (fun q' t' => EY (fun y => supplyUtil (y + (L - 1) * q + q'))
      - EY (fun y => supplyUtil (y + (L - 1) * q)) - t') q' t' =
      (fun q' => EY (fun y => supplyUtil (y + (L - 1) * q + q'))
      - EY (fun y => supplyUtil (y + (L - 1) * q))) q' - t' := fun _ _ => rfl
  have hSS : ∀ q' t', (fun q' t' => t' - P.c * q') q' t' = t' - (fun q' => P.c * q') q' :=
    fun _ _ => rfl
  constructor
  · intro h
    obtain ⟨hq, hpos, hmax, ht⟩ := nbs_nec hg0 hg1 hB hSS
      (fun q' hq' => mul_nonneg hc0.le (Set.mem_Ici.mp hq')) h
    simp only [EY_shift] at hpos hmax ht
    have hq0 : 0 ≤ q := hq
    have hX0 : 0 ≤ (L - 1) * q := mul_nonneg (by linarith) hq0
    have hW0 : EY (fun y => supplyUtil (y + (L - 1) * q)) = Wf ((L - 1) * q) := rfl
    rw [hW0] at hpos hmax ht
    set X := (L - 1) * q with hX
    have hQ : X + q = L * q := by rw [hX]; ring
    have hLq : L * q = 1 - s := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · set h := (1 - s - L * q) / 2 with hh
        have hhpos : 0 < h := by rw [hh]; linarith
        have hm := hmax (q + h) (Set.mem_Ici.mpr (by linarith))
        have ht1 := W_tangent (L * q + h) (L * q)
        rw [D_formula (by nlinarith), max_eq_right (by linarith)] at ht1
        have e1 : X + (q + h) = L * q + h := by linarith
        rw [e1, hQ] at hm
        have : P.c * h < h * (1 - (L * q + h)) ^ 2 := by
          rw [← h2]
          have : s < 1 - (L * q + h) := by linarith
          have : s ^ 2 < (1 - (L * q + h)) ^ 2 := by nlinarith
          nlinarith
        nlinarith
      · have hqpos : 0 < q := by
          by_contra hq'; push_neg at hq'
          have : L * q ≤ 0 := by nlinarith
          linarith
        set h := min q ((L * q - (1 - s)) / 2) with hh
        have hhpos : 0 < h := lt_min hqpos (by linarith)
        have hhq : h ≤ q := min_le_left _ _
        have hh2 : h ≤ (L * q - (1 - s)) / 2 := min_le_right _ _
        have hm := hmax (q - h) (Set.mem_Ici.mpr (by linarith))
        have ht1 := W_tangent (L * q - h) (L * q)
        have hQh : 0 ≤ L * q - h := by nlinarith
        rw [D_formula hQh] at ht1
        have e1 : X + (q - h) = L * q - h := by linarith
        rw [e1, hQ] at hm
        have hmx : max 0 (1 - (L * q - h)) < s := max_lt h0 (by linarith)
        have hmx0 : 0 ≤ max 0 (1 - (L * q - h)) := le_max_left _ _
        have : (max 0 (1 - (L * q - h))) ^ 2 < P.c := by rw [← h2]; nlinarith
        nlinarith
    have hqv : q = (1 - s) / L := by field_simp; linarith
    refine ⟨hqv, ?_⟩
    have hsur := fwd_surplus P hS L hL
    rw [← hs, ← hqv, hQ] at hsur
    rw [hQ] at ht
    have hqpos : 0 < q := by rw [hqv]; apply div_pos <;> linarith
    rw [ht (by rw [hsur]; positivity), hsur]
  · rintro ⟨hqv, htv⟩
    have hq0 : 0 ≤ q := by rw [hqv]; apply div_nonneg <;> linarith
    have hsur := fwd_surplus P hS L hL
    rw [← hs, ← hqv] at hsur
    have hQ : (L - 1) * q + q = 1 - s := by rw [hqv]; field_simp; ring
    apply nbs_suff hg0 hg1 hB hSS (Set.mem_Ici.mpr hq0) (by positivity)
    · simp only [EY_shift]
      show 0 ≤ Wf ((L - 1) * q + q) - Wf ((L - 1) * q) - P.c * q
      rw [hsur]; positivity
    · intro q' hq'
      simp only [EY_shift]
      show Wf ((L - 1) * q + q') - Wf ((L - 1) * q) - P.c * q' ≤
        Wf ((L - 1) * q + q) - Wf ((L - 1) * q) - P.c * q
      have ht1 := W_tangent ((L - 1) * q + q) ((L - 1) * q + q')
      rw [hQ, D_formula (by linarith), max_eq_right (by linarith), sub_sub_cancel, h2] at ht1
      rw [hQ]
      nlinarith
    · simp only [EY_shift]
      show t = P.c * q + (1 - P.γ) * (Wf ((L - 1) * q + q) - Wf ((L - 1) * q) - P.c * q)
      rw [hsur, htv]

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma min_max_comm {k z : ℝ} (hk : 0 ≤ k) : min k (max 0 z) = max 0 (min k z) := by
  rcases le_total z 0 with h | h
  · rw [max_eq_left h, min_eq_right hk, max_eq_left (le_trans (min_le_right _ _) h)]
  · rw [max_eq_right h, max_eq_right (le_min hk h)]

/-- Equation (A.2) without forward suppliers, general other-supplier total `O`. -/
theorem stage_iff {γ k y O q t : ℝ} (h0 : 0 < γ) (h1 : γ < 1) (hk : 0 ≤ k)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (hO : 0 ≤ O) :
    AdHocBargain γ k O y q t ↔
      q = max 0 (min k (1 - y - O)) ∧
      t = (1 - γ) * (supplyUtil (y + O + q) - supplyUtil (y + O)) := by
  have hB : ∀ q' t', (fun q' t' => supplyUtil (y + O + q') - supplyUtil (y + O) - t') q' t' =
      (fun q' => supplyUtil (y + O + q') - supplyUtil (y + O)) q' - t' := fun _ _ => rfl
  have hSS : ∀ q' t', (fun (_ : ℝ) (t' : ℝ) => t') q' t' = t' - (fun _ => (0 : ℝ)) q' :=
    fun _ t' => (sub_zero t').symm
  set m := max 0 (min k (1 - y - O)) with hm
  have hA : Set.Icc 0 (min k (max 0 (1 - y - O))) = Set.Icc 0 m := by rw [min_max_comm hk]
  have hm0 : 0 ≤ m := le_max_left _ _
  have hmpos : 0 < m → m ≤ 1 - y - O := by
    intro hp
    rw [hm] at hp ⊢
    rcases le_total (min k (1 - y - O)) 0 with h | h
    · rw [max_eq_left h] at hp; linarith
    · rw [max_eq_right h]; exact min_le_right _ _
  unfold AdHocBargain
  rw [hA]
  constructor
  · intro h
    have hgB := h.2.2.1
    have hgS := h.2.2.2.1
    obtain ⟨hq, hpos, hmax, ht⟩ := nbs_nec h0 h1 hB hSS (fun _ _ => le_refl 0) h
    simp only [sub_zero] at hpos hmax ht hgB hgS
    have hqm : q = m := by
      by_contra hne
      have hlt : q < m := lt_of_le_of_ne hq.2 hne
      have hmp : 0 < m := lt_of_le_of_lt hq.1 hlt
      have := hmpos hmp
      have hs := g_strict (x := y + O + q) (x' := y + O + m) (by linarith) (by linarith)
      have := hmax m ⟨hm0, le_refl _⟩
      linarith
    refine ⟨hqm, ?_⟩
    rcases lt_or_eq_of_le hpos with hp | hp
    · rw [ht hp]; ring
    · rw [← hp]; linarith
  · rintro ⟨hqm, ht⟩
    apply nbs_suff h0 h1 hB hSS (q := q) (by rw [hqm]; exact ⟨hm0, le_refl _⟩) (le_refl 0)
    · simp only [sub_zero]
      linarith [g_mono (x := y + O) (x' := y + O + q) (by rw [hqm]; linarith)]
    · intro q' hq'
      simp only [sub_zero]
      have := g_mono (x := y + O + q') (x' := y + O + q) (by rw [hqm]; linarith [hq'.2])
      linarith
    · simp only [sub_zero]; rw [ht]; ring

/-- the symmetric fixed point -/
theorem sym_iff {k y q : ℝ} (L : ℝ) (hL : 1 ≤ L) (hk : 0 ≤ k) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    q = max 0 (min k (1 - y - (L - 1) * q)) ↔ q = min k ((1 - y) / L) := by
  have hLpos : 0 < L := by linarith
  set w := (1 - y) / L with hw
  have hLw : L * w = 1 - y := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by rw [hw]; apply div_nonneg <;> linarith [hy.2]
  constructor
  · intro h
    have hq0 : 0 ≤ q := by rw [h]; exact le_max_left _ _
    rcases le_total (min k (1 - y - (L - 1) * q)) 0 with h1 | h1
    · rw [max_eq_left h1] at h
      subst h
      simp only [mul_zero, sub_zero] at h1
      rcases le_total k (1 - y) with h2 | h2
      · rw [min_eq_left h2] at h1
        have : k = 0 := le_antisymm h1 hk
        rw [this, min_eq_left hw0]
      · rw [min_eq_right h2] at h1
        have : w = 0 := by nlinarith
        rw [this, min_eq_right hk]
    · rw [max_eq_right h1] at h
      rcases le_total k (1 - y - (L - 1) * q) with h2 | h2
      · rw [min_eq_left h2] at h
        subst h
        rw [min_eq_left]; nlinarith
      · rw [min_eq_right h2] at h
        have hqw : q = w := by nlinarith
        rw [hqw, min_eq_right]; nlinarith
  · intro h
    rcases le_total k w with h2 | h2
    · rw [min_eq_left h2] at h
      subst h
      have : q ≤ 1 - y - (L - 1) * q := by nlinarith
      rw [min_eq_left this, max_eq_right hk]
    · rw [min_eq_right h2] at h
      subst h
      have e : 1 - y - (L - 1) * w = w := by linarith
      rw [e, min_eq_right h2, max_eq_right hw0]

end G2GImport.Sourcing


namespace G2GImport.Sourcing

noncomputable def qe (L k y : ℝ) : ℝ := min k ((1 - y) / L)
noncomputable def Oe (L k y : ℝ) : ℝ := (L - 1) * qe L k y
noncomputable def tau (γ L k k' y : ℝ) : ℝ :=
  (1 - γ) * (supplyUtil (y + Oe L k y + k') - supplyUtil (y + Oe L k y))

lemma qe_cont (L k : ℝ) : Continuous (fun y => qe L k y) := by
  unfold qe; fun_prop

lemma tau_cont (γ L k k' : ℝ) : Continuous (fun y => tau γ L k k' y) := by
  unfold tau Oe
  have := qe_cont L k
  have c1 : Continuous (fun y => y + (L - 1) * qe L k y + k') := by fun_prop
  have c2 : Continuous (fun y => y + (L - 1) * qe L k y) := by fun_prop
  exact continuous_const.mul ((g_cont.comp c1).sub (g_cont.comp c2))

lemma O_bound {L k y : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Oe L k y ∧ y + Oe L k y ≤ 1 := by
  have hLpos : 0 < L := by linarith
  have hw0 : 0 ≤ (1 - y) / L := by apply div_nonneg <;> linarith [hy.2]
  have hLw : L * ((1 - y) / L) = 1 - y := by field_simp
  have hq0 : 0 ≤ qe L k y := le_min hk hw0
  have hqw : qe L k y ≤ (1 - y) / L := min_le_right _ _
  unfold Oe
  constructor
  · exact mul_nonneg (by linarith) hq0
  · nlinarith

lemma g_cap {x k' : ℝ} (hx : x ≤ 1) (hk : 0 ≤ k') :
    supplyUtil (x + max 0 (min k' (1 - x))) = supplyUtil (x + k') := by
  rw [max_eq_right (le_min hk (by linarith))]
  rw [← g_min1 (x + k')]
  congr 1
  rcases le_total k' (1 - x) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma P1 {L k y h : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) :
    max 0 (1 - (y + Oe L k y + (k + h))) = max 0 (1 - y - (L * k + h)) := by
  have hLpos : 0 < L := by linarith
  have hLw : L * ((1 - y) / L) = 1 - y := by field_simp
  unfold Oe qe
  rcases le_total k ((1 - y) / L) with h1 | h1
  · rw [min_eq_left h1]; ring_nf
  · rw [min_eq_right h1]
    rw [max_eq_left (by nlinarith), max_eq_left (by nlinarith)]

lemma P2 {L k y h : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hh : 0 ≤ h) :
    max 0 (1 - (y + Oe L k y + (k - h))) ≤ max 0 (1 - y - L * k) + h := by
  have hLpos : 0 < L := by linarith
  have hLw : L * ((1 - y) / L) = 1 - y := by field_simp
  unfold Oe qe
  rcases le_total k ((1 - y) / L) with h1 | h1
  · rw [min_eq_left h1]
    have e : 1 - (y + (L - 1) * k + (k - h)) = (1 - y - L * k) + h := by ring
    rw [e]
    exact max_le (by positivity) (by linarith [le_max_right 0 (1 - y - L * k)])
  · rw [min_eq_right h1]
    exact max_le (by positivity) (by nlinarith [le_max_left 0 (1 - y - L * k)])

lemma tau_tangent (γ : ℝ) (hγ : γ < 1) (L k k1 k2 : ℝ) :
    EY (fun y => tau γ L k k2 y) ≤ EY (fun y => tau γ L k k1 y) +
      (1 - γ) * (k2 - k1) * ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - (y + Oe L k y + k1)) := by
  unfold EY
  have c3 : Continuous (fun y => 2 * max 0 (1 - (y + Oe L k y + k1))) := by
    unfold Oe; have := qe_cont L k; fun_prop
  have c4 : Continuous (fun y => (1 - γ) * (k2 - k1) * (2 * max 0 (1 - (y + Oe L k y + k1)))) :=
    continuous_const.mul c3
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((tau_cont γ L k k1).intervalIntegrable _ _)
      (c4.intervalIntegrable _ _)]
  apply intervalIntegral.integral_mono_on (by norm_num) ((tau_cont γ L k k2).intervalIntegrable _ _)
    (((tau_cont γ L k k1).add c4).intervalIntegrable _ _)
  intro y _
  have := g_tangent (y + Oe L k y + k1) (y + Oe L k y + k2)
  simp only [Pi.add_apply]
  unfold tau
  have h1 : 0 < 1 - γ := by linarith
  have e : y + Oe L k y + k2 - (y + Oe L k y + k1) = k2 - k1 := by ring
  rw [e] at this
  nlinarith [this]

lemma int_P1 {L k h : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) (hh : 0 ≤ h) :
    ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - (y + Oe L k y + (k + h))) = Df (L * k + h) := by
  unfold Df
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by norm_num)] at hy
  simp only
  rw [P1 hL hk hy hh]

lemma int_P2 {L k h : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) (hh : 0 ≤ h) :
    ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - (y + Oe L k y + (k - h))) ≤ Df (L * k) + 2 * h := by
  unfold Df
  have c3 : Continuous (fun y => 2 * max 0 (1 - (y + Oe L k y + (k - h)))) := by
    unfold Oe; have := qe_cont L k; fun_prop
  have : (∫ y in (0 : ℝ)..1, 2 * max 0 (1 - y - L * k)) + 2 * h =
      ∫ y in (0 : ℝ)..1, (2 * max 0 (1 - y - L * k) + 2 * h) := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp
  rw [this]
  apply intervalIntegral.integral_mono_on (by norm_num) (c3.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; fun_prop)
  intro y hy
  have := P2 hL hk hy hh
  linarith

lemma int_P0 {L k : ℝ} (hL : 1 ≤ L) (hk : 0 ≤ k) :
    ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - (y + Oe L k y + k)) = Df (L * k) := by
  have := int_P1 hL hk (le_refl 0)
  simpa only [add_zero] using this

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma r_facts (P : Params) (hS : P.Standing) :
    0 < Real.sqrt (P.c / (1 - P.γ)) ∧ Real.sqrt (P.c / (1 - P.γ)) < 1 ∧
    (1 - P.γ) * Real.sqrt (P.c / (1 - P.γ)) ^ 2 = P.c := by
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS
  have h1g : 0 < 1 - P.γ := by linarith
  have hpos : 0 < P.c / (1 - P.γ) := div_pos hc0 h1g
  have hlt : P.c / (1 - P.γ) < 1 := (div_lt_one h1g).mpr hc1
  have h2 : Real.sqrt (P.c / (1 - P.γ)) ^ 2 = P.c / (1 - P.γ) := Real.sq_sqrt hpos.le
  have h0 : 0 < Real.sqrt (P.c / (1 - P.γ)) := Real.sqrt_pos.mpr hpos
  refine ⟨h0, by nlinarith, ?_⟩
  rw [h2]; field_simp

lemma bargain_q_nonneg {γ k O y q t : ℝ} (h : AdHocBargain γ k O y q t) : 0 ≤ q := h.1.1

/-- pointwise structure of any symmetric ad hoc equilibrium -/
lemma eq_pointwise (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P l k q t) : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      q y = qe (l : ℝ) k y ∧ t y = tau P.γ (l : ℝ) k k y := by
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  intro y hy
  have hb := heq.2.1 y hy
  have hq0 := bargain_q_nonneg hb
  have hO : 0 ≤ ((l : ℝ) - 1) * q y := mul_nonneg (by linarith) hq0
  obtain ⟨hq, ht⟩ := (stage_iff hg0 hg1 heq.1 hy hO).mp hb
  have hqe : q y = qe (l : ℝ) k y := (sym_iff (l : ℝ) hL heq.1 hy).mp hq
  refine ⟨hqe, ?_⟩
  have hOe : ((l : ℝ) - 1) * q y = Oe (l : ℝ) k y := by unfold Oe; rw [hqe]
  rw [hOe] at hq ht
  have hb2 := (O_bound hL heq.1 hy).2
  have e : 1 - y - Oe (l : ℝ) k y = 1 - (y + Oe (l : ℝ) k y) := by ring
  rw [e] at hq
  rw [ht, hq, g_cap hb2 heq.1]
  rfl

/-- any deviation outcome has the `tau` payment -/
lemma dev_any (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (hk : 0 ≤ k)
    (q : ℝ → ℝ) (hq : ∀ y ∈ Set.Icc (0 : ℝ) 1, q y = qe (l : ℝ) k y)
    (k' : ℝ) (hk' : 0 ≤ k') (q' t' : ℝ → ℝ)
    (hb : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      AdHocBargain P.γ k' (((l : ℝ) - 1) * q y) y (q' y) (t' y)) :
    EY t' = EY (fun y => tau P.γ (l : ℝ) k k' y) := by
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  unfold EY
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by norm_num)] at hy
  have hOe : ((l : ℝ) - 1) * q y = Oe (l : ℝ) k y := by unfold Oe; rw [hq y hy]
  have hb' := hb y hy
  rw [hOe] at hb'
  obtain ⟨h1, h2⟩ := (stage_iff hg0 hg1 hk' hy (O_bound hL hk hy).1).mp hb'
  have e : 1 - y - Oe (l : ℝ) k y = 1 - (y + Oe (l : ℝ) k y) := by ring
  rw [e] at h1
  simp only
  rw [h2, h1, g_cap (O_bound hL hk hy).2 hk']
  rfl

/-- deviations exist -/
lemma dev_exists (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (hk : 0 ≤ k)
    (q : ℝ → ℝ) (hq : ∀ y ∈ Set.Icc (0 : ℝ) 1, q y = qe (l : ℝ) k y)
    (k' : ℝ) (hk' : 0 ≤ k') : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      AdHocBargain P.γ k' (((l : ℝ) - 1) * q y) y
        ((fun y => max 0 (min k' (1 - y - ((l : ℝ) - 1) * q y))) y)
        ((fun y => (1 - P.γ) * (supplyUtil (y + ((l : ℝ) - 1) * q y +
          max 0 (min k' (1 - y - ((l : ℝ) - 1) * q y))) -
          supplyUtil (y + ((l : ℝ) - 1) * q y))) y) := by
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  intro y hy
  have hOe : ((l : ℝ) - 1) * q y = Oe (l : ℝ) k y := by unfold Oe; rw [hq y hy]
  beta_reduce
  rw [hOe]
  exact (stage_iff hg0 hg1 hk' hy (O_bound hL hk hy).1).mpr ⟨rfl, rfl⟩

theorem adhoc_nec (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P l k q t) :
    k = (1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ) := by
  have hpw := eq_pointwise P hS l hl k q t heq
  obtain ⟨r0, r1, hr2⟩ := r_facts P hS
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  set r := Real.sqrt (P.c / (1 - P.γ)) with hr
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hk := heq.1
  have hEt : EY t = EY (fun y => tau P.γ L k k y) := by
    unfold EY
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    exact (hpw y hy).2
  have hdev : ∀ k', 0 ≤ k' → EY (fun y => tau P.γ L k k' y) - P.c * k' ≤
      EY (fun y => tau P.γ L k k y) - P.c * k := by
    intro k' hk'
    have := heq.2.2 k' hk' _ _ (dev_exists P hS l hl k hk q (fun y hy => (hpw y hy).1) k' hk')
    rw [dev_any P hS l hl k hk q (fun y hy => (hpw y hy).1) k' hk' _ _
      (dev_exists P hS l hl k hk q (fun y hy => (hpw y hy).1) k' hk'), hEt] at this
    exact this
  have h1g : 0 < 1 - P.γ := by linarith
  have hLk : L * k = 1 - r := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · set h := (1 - r - L * k) / 2 with hh
      have hhpos : 0 < h := by rw [hh]; linarith
      have ht1 := tau_tangent P.γ hg1 L k (k + h) k
      rw [int_P1 hL hk hhpos.le, D_formula (by nlinarith), max_eq_right (by linarith)] at ht1
      have hd := hdev (k + h) (by linarith)
      have : P.c * h < (1 - P.γ) * h * (1 - (L * k + h)) ^ 2 := by
        rw [← hr2]
        have : r < 1 - (L * k + h) := by linarith
        have : r ^ 2 < (1 - (L * k + h)) ^ 2 := by nlinarith
        have := mul_lt_mul_of_pos_left this (mul_pos h1g hhpos)
        nlinarith
      nlinarith
    · have hkpos : 0 < k := by
        by_contra hk'; push Not at hk'
        have : L * k ≤ 0 := by nlinarith
        linarith
      set m := max 0 (1 - L * k) with hm
      have hm0 : 0 ≤ m := le_max_left _ _
      have hmr : m < r := max_lt r0 (by linarith)
      set h := min k ((r ^ 2 - m ^ 2) / 4) with hh
      have hgap : 0 < r ^ 2 - m ^ 2 := by nlinarith
      have hhpos : 0 < h := lt_min hkpos (by linarith)
      have hhk : h ≤ k := min_le_left _ _
      have hh2 : h ≤ (r ^ 2 - m ^ 2) / 4 := min_le_right _ _
      have ht1 := tau_tangent P.γ hg1 L k (k - h) k
      have hI := int_P2 hL hk hhpos.le
      rw [D_formula (by nlinarith)] at hI
      have hd := hdev (k - h) (by linarith)
      have e : k - (k - h) = h := by ring
      rw [e] at ht1
      have : (1 - P.γ) * h * ∫ y in (0 : ℝ)..1, 2 * max 0 (1 - (y + Oe L k y + (k - h))) ≤
          (1 - P.γ) * h * (m ^ 2 + 2 * h) :=
        mul_le_mul_of_nonneg_left hI (mul_pos h1g hhpos).le
      have : (1 - P.γ) * h * (m ^ 2 + 2 * h) < P.c * h := by
        rw [← hr2]
        have : m ^ 2 + 2 * h < r ^ 2 := by linarith
        have := mul_lt_mul_of_pos_left this (mul_pos h1g hhpos)
        nlinarith
      nlinarith
  field_simp
  linarith

theorem adhoc_exists (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) :
    IsAdHocEq P l ((1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ))
      (fun y => qe (l : ℝ) ((1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ)) y)
      (fun y => tau P.γ (l : ℝ) ((1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ))
        ((1 - Real.sqrt (P.c / (1 - P.γ))) / (l : ℝ)) y) := by
  obtain ⟨r0, r1, hr2⟩ := r_facts P hS
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  set r := Real.sqrt (P.c / (1 - P.γ)) with hr
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  set k := (1 - r) / L with hkdef
  have hk : 0 ≤ k := by rw [hkdef]; apply div_nonneg <;> linarith
  have hLk : L * k = 1 - r := by rw [hkdef]; field_simp
  refine ⟨hk, ?_, ?_⟩
  · intro y hy
    have hsym : qe L k y = max 0 (min k (1 - y - (L - 1) * qe L k y)) :=
      (sym_iff L hL hk hy).mpr rfl
    apply (stage_iff hg0 hg1 hk hy (O_bound hL hk hy).1).mpr
    refine ⟨hsym, ?_⟩
    simp only
    unfold tau
    have e : 1 - y - (L - 1) * qe L k y = 1 - (y + Oe L k y) := by unfold Oe; ring
    have hcap := g_cap (O_bound hL hk hy).2 hk
    rw [← e] at hcap
    unfold Oe at hcap ⊢
    rw [← hsym] at hcap
    rw [hcap]
  · intro k' hk' q' t' hb
    rw [dev_any P hS l hl k hk _ (fun y _ => rfl) k' hk' q' t' hb]
    have ht1 := tau_tangent P.γ hg1 L k k k'
    rw [int_P0 hL hk, hLk, D_formula (by linarith), max_eq_right (by linarith),
      sub_sub_cancel] at ht1
    nlinarith

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma tau_integral (γ L k : ℝ) (hL : 1 ≤ L) (hk : 0 ≤ k) (ha : L * k ≤ 1) :
    EY (fun y => tau γ L k k y) =
      (1 - γ) * (k * (1 - L * k) ^ 2 + k ^ 2 * (1 - L * k) + (L * k) ^ 3 / (3 * L ^ 2)) := by
  have hLpos : 0 < L := by linarith
  unfold EY
  rw [int_split (f := fun y => tau γ L k k y)
    (f1 := fun y => (1 - γ) * (2 * k - 2 * (L * k) * k + k ^ 2) + ((1 - γ) * (-2 * k)) * y
      + 0 * y ^ 2)
    (f2 := fun y => (1 - γ) / L ^ 2 + ((1 - γ) / L ^ 2 * (-2)) * y + ((1 - γ) / L ^ 2) * y ^ 2)
    (tau_cont γ L k k) (m := 1 - L * k) (by linarith) (by nlinarith)]
  · rw [int_quad, int_quad]
    field_simp
    ring
  · intro y hy0 hy
    have hkw : k ≤ (1 - y) / L := by rw [le_div_iff₀ hLpos]; linarith
    unfold tau Oe qe
    rw [min_eq_left hkw, g_le1 (by nlinarith), g_le1 (by nlinarith)]
    ring
  · intro y hy hy1
    have hkw : (1 - y) / L ≤ k := by rw [div_le_iff₀ hLpos]; linarith
    have hLw : L * ((1 - y) / L) = 1 - y := by field_simp
    unfold tau Oe qe
    rw [min_eq_right hkw, g_ge1 (by nlinarith), g_le1 (by nlinarith)]
    field_simp
    ring

lemma g_Lqe (L k y : ℝ) (hL : 1 ≤ L) (hy : y ≤ 1) :
    supplyUtil (y + L * qe L k y) = supplyUtil (y + L * k) := by
  have hLpos : 0 < L := by linarith
  have hLw : L * ((1 - y) / L) = 1 - y := by field_simp
  unfold qe
  rw [← g_min1 (y + L * k)]
  congr 1
  rcases le_total k ((1 - y) / L) with h | h
  · rw [min_eq_left h, min_eq_left]; nlinarith
  · rw [min_eq_right h, hLw, min_eq_right]; ring; nlinarith

theorem adhoc_vals (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P l k q t) :
    adHocBuyer l q t = (1 - Real.sqrt (P.c / (1 - P.γ)) ^ 3 / 3
        - (1 - P.γ) * (1 - Real.sqrt (P.c / (1 - P.γ))) * Real.sqrt (P.c / (1 - P.γ)) ^ 2)
        - (1 - P.γ) * ((1 - Real.sqrt (P.c / (1 - P.γ))) ^ 2 * Real.sqrt (P.c / (1 - P.γ))
          + (1 - Real.sqrt (P.c / (1 - P.γ))) ^ 3 / 3) / (l : ℝ) ∧
    adHocSupplier P k t =
      (1 - P.γ) * ((1 - Real.sqrt (P.c / (1 - P.γ))) ^ 2 * Real.sqrt (P.c / (1 - P.γ))
          + (1 - Real.sqrt (P.c / (1 - P.γ))) ^ 3 / 3) / (l : ℝ) ^ 2 := by
  have hpw := eq_pointwise P hS l hl k q t heq
  have hkv := adhoc_nec P hS l hl k q t heq
  obtain ⟨r0, r1, hr2⟩ := r_facts P hS
  set r := Real.sqrt (P.c / (1 - P.γ)) with hr
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hk := heq.1
  have hLk : L * k = 1 - r := by rw [hkv]; field_simp
  have hEt : EY t = EY (fun y => tau P.γ L k k y) := by
    unfold EY
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by norm_num)] at hy
    exact (hpw y hy).2
  have hTI := tau_integral P.γ L k hL hk (by linarith)
  rw [hLk] at hTI
  constructor
  · have hB : adHocBuyer l q t =
        EY (fun y => supplyUtil (y + L * qe L k y) - L * tau P.γ L k k y) := by
      unfold adHocBuyer EY
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      simp only
      rw [(hpw y hy).1, (hpw y hy).2]
    rw [hB]
    have hB2 : EY (fun y => supplyUtil (y + L * qe L k y) - L * tau P.γ L k k y) =
        Wf (L * k) - L * EY (fun y => tau P.γ L k k y) := by
      have c1 : Continuous (fun y => supplyUtil (y + L * qe L k y)) :=
        g_cont.comp (continuous_id.add (continuous_const.mul (qe_cont L k)))
      have c2 : Continuous (fun y => L * tau P.γ L k k y) :=
        continuous_const.mul (tau_cont P.γ L k k)
      unfold EY Wf
      rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
      congr 1
      unfold EY
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      exact g_Lqe L k y hL hy.2
    rw [hB2, hTI, hLk, W_formula (by linarith) (by linarith)]
    have hk' : k = (1 - r) / L := by field_simp; linarith
    rw [hk']
    field_simp
    ring
  · unfold adHocSupplier
    rw [hEt, hTI, ← hr2]
    have hk' : k = (1 - r) / L := by field_simp; linarith
    rw [hk']
    field_simp
    ring

theorem fwd_vals (P : Params) (hS : P.Standing) (l : ℕ) (hl : 1 ≤ l) (q t : ℝ)
    (heq : IsForwardEq P l q t) :
    fwdBuyer l q t = (1 - Real.sqrt P.c ^ 3 / 3 - P.c * (1 - Real.sqrt P.c))
      - (1 - P.γ) * (Real.sqrt P.c * (1 - Real.sqrt P.c) ^ 2 / (l : ℝ)
        + (1 - Real.sqrt P.c) ^ 3 / (3 * (l : ℝ) ^ 2)) ∧
    fwdSupplier P q t = (1 - P.γ) * (Real.sqrt P.c * (1 - Real.sqrt P.c) ^ 2 / (l : ℝ) ^ 2
        + (1 - Real.sqrt P.c) ^ 3 / (3 * (l : ℝ) ^ 3)) := by
  obtain ⟨hqv, htv⟩ := (fwd_char P hS l hl q t).mp heq
  obtain ⟨h0, h1, h2⟩ := sqrt_facts P hS
  set s := Real.sqrt P.c with hs
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  have hLq : L * q = 1 - s := by rw [hqv]; field_simp
  constructor
  · unfold fwdBuyer
    have : EY (fun y => supplyUtil (y + L * q)) = Wf (L * q) := rfl
    rw [this, hLq, W_formula (by linarith) (by linarith), htv, hqv]
    field_simp
    ring
  · unfold fwdSupplier
    rw [htv, hqv]
    field_simp
    ring

end G2GImport.Sourcing


namespace G2GImport.Sourcing

lemma rp32 {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = Real.sqrt x ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

theorem closed_payoffs_pf (P : Params) (hS : P.Standing)
    (l : ℕ) (hl : 1 ≤ l) :
    (∀ k q t, IsAdHocEq P l k q t →
      adHocBuyer l q t = adHocBuyerClosed P (l : ℝ) ∧
      adHocSupplier P k t = adHocSupplierClosed P (l : ℝ)) ∧
    (∀ q t, IsForwardEq P l q t →
      fwdBuyer l q t = fwdBuyerClosed P (l : ℝ) ∧
      fwdSupplier P q t = fwdSupplierClosed P (l : ℝ)) := by
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  have h1g : 0 < 1 - P.γ := by linarith
  have hL : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hLpos : (0 : ℝ) < (l : ℝ) := by linarith
  constructor
  · intro k q t h
    obtain ⟨b, s⟩ := adhoc_vals P hS l hl k q t h
    obtain ⟨r0, r1, hr2⟩ := r_facts P hS
    unfold adHocBuyerClosed adHocSupplierClosed
    rw [b, s, rp32 (div_nonneg hc0.le h1g.le)]
    set r := Real.sqrt (P.c / (1 - P.γ))
    rw [← hr2]
    constructor
    · field_simp; ring
    · field_simp; ring
  · intro q t h
    obtain ⟨b, s⟩ := fwd_vals P hS l hl q t h
    obtain ⟨s0, s1, hs2⟩ := sqrt_facts P hS
    unfold fwdBuyerClosed fwdSupplierClosed
    rw [b, s, rp32 hc0.le]
    set s := Real.sqrt P.c
    rw [← hs2]
    constructor
    · field_simp; ring
    · field_simp; ring

theorem lemma_2_pf (P : Params) (hS : P.Standing) (q t : ℝ)
    (heq : IsForwardEq P 1 q t) :
    q = 1 - Real.sqrt P.c ∧
    t = (3 * P.c * P.γ - P.γ + 1 -
      (2 * P.γ + 1) * P.c ^ ((3 : ℝ) / 2)) / 3 ∧
    fwdBuyer 1 q t =
      (2 * P.c ^ ((3 : ℝ) / 2) * P.γ - 3 * P.c * P.γ + P.γ + 2) / 3 ∧
    fwdSupplier P q t =
      (1 - Real.sqrt P.c) * (Real.sqrt P.c + 1 - 2 * P.c) * (1 - P.γ) / 3 := by
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  obtain ⟨hq, ht⟩ := (fwd_char P hS 1 le_rfl q t).mp heq
  obtain ⟨bb, ss⟩ := fwd_vals P hS 1 le_rfl q t heq
  obtain ⟨s0, s1, hs2⟩ := sqrt_facts P hS
  simp only [Nat.cast_one, div_one] at hq bb ss
  rw [rp32 hc0.le]
  generalize Real.sqrt P.c = s at *
  refine ⟨hq, ?_, ?_, ?_⟩
  · rw [ht, hq, ← hs2]; ring
  · rw [bb, ← hs2]; ring
  · rw [ss, ← hs2]; ring

lemma EY_qe (L k : ℝ) (hL : 1 ≤ L) (hk : 0 ≤ k) (ha : L * k ≤ 1) :
    EY (fun y => qe L k y) = k * (1 - L * k) + L * k ^ 2 / 2 := by
  have hLpos : 0 < L := by linarith
  unfold EY
  rw [int_split (f := fun y => qe L k y) (f1 := fun y => k + 0 * y + 0 * y ^ 2)
    (f2 := fun y => 1 / L + (-1 / L) * y + 0 * y ^ 2)
    (qe_cont L k) (m := 1 - L * k) (by linarith) (by nlinarith)]
  · rw [int_quad, int_quad]; field_simp; ring
  · intro y _ hy
    have hkw : k ≤ (1 - y) / L := by rw [le_div_iff₀ hLpos]; linarith
    unfold qe; rw [min_eq_left hkw]; ring
  · intro y hy _
    have hkw : (1 - y) / L ≤ k := by rw [div_le_iff₀ hLpos]; linarith
    unfold qe; rw [min_eq_right hkw]; field_simp; ring

theorem lemma_1_pf (P : Params) (hS : P.Standing) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P 1 k q t) :
    k = 1 - Real.sqrt (P.c / (1 - P.γ)) ∧
    EY q = (1 - P.c / (1 - P.γ)) / 2 ∧
    EY t = (1 - P.c * Real.sqrt (P.c / (1 - P.γ)) - P.γ) / 3 ∧
    adHocBuyer 1 q t =
      (2 - P.c * P.γ * Real.sqrt (P.c / (1 - P.γ)) - P.γ - P.γ ^ 2) /
        (3 * (1 - P.γ)) ∧
    adHocSupplier P k t =
      (P.c * (2 * Real.sqrt (P.c / (1 - P.γ)) - 3) + 1 - P.γ) / 3 := by
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  have h1g : 0 < 1 - P.γ := by linarith
  have hk := adhoc_nec P hS 1 le_rfl k q t heq
  have hpw := eq_pointwise P hS 1 le_rfl k q t heq
  obtain ⟨b, s⟩ := adhoc_vals P hS 1 le_rfl k q t heq
  obtain ⟨r0, r1, hr2⟩ := r_facts P hS
  have hr2' : Real.sqrt (P.c / (1 - P.γ)) ^ 2 = P.c / (1 - P.γ) :=
    Real.sq_sqrt (div_nonneg hc0.le h1g.le)
  simp only [Nat.cast_one, div_one] at hk b s hpw
  have hEq : EY q = EY (fun y => qe 1 k y) := by
    unfold EY; apply intervalIntegral.integral_congr
    intro y hy; rw [Set.uIcc_of_le (by norm_num)] at hy; exact (hpw y hy).1
  have hEt : EY t = EY (fun y => tau P.γ 1 k k y) := by
    unfold EY; apply intervalIntegral.integral_congr
    intro y hy; rw [Set.uIcc_of_le (by norm_num)] at hy; exact (hpw y hy).2
  have hk0 : 0 ≤ k := heq.1
  rw [hEq, EY_qe 1 k le_rfl hk0 (by rw [hk]; linarith), hEt,
    tau_integral P.γ 1 k le_rfl hk0 (by rw [hk]; linarith), b, s, hk]
  set r := Real.sqrt (P.c / (1 - P.γ))
  rw [← hr2']
  rw [← hr2]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · field_simp; ring
  · ring

/-- `D₂` as an explicit quadratic -/
lemma D2_quad (P : Params) (l : ℝ) :
    D₂ P l = (2 * (1 - P.γ) + (3 * P.γ - 2) * Real.sqrt (1 / (1 - P.γ))) *
        P.c ^ ((3 : ℝ) / 2) * l ^ 2 +
      (-3 * (P.γ - 1) ^ 2 * P.c ^ ((3 : ℝ) / 2) - 3 * Real.sqrt P.c * (P.γ - 1) ^ 2
        - P.c * (P.γ - 1) * (2 * Real.sqrt (P.c / (1 - P.γ)) - 6 * P.γ + 3)
        + (P.γ - 1) ^ 2) * l +
      ((P.γ - 1) * P.c ^ ((3 : ℝ) / 2) * (P.γ - 1) + 3 * Real.sqrt P.c * (P.γ - 1) ^ 2
        - 3 * P.c * (P.γ - 1) ^ 2 - (P.γ - 1) ^ 2) := by
  unfold D₂; ring

theorem D2_root_pf (P : Params) (hS : P.Standing) :
    (∀ l : ℝ, 0 < l →
      fwdBuyerClosed P l - adHocBuyerClosed P l =
        D₂ P l / (3 * (1 - P.γ) * l ^ 2)) ∧
    0 < (2 * (1 - P.γ) + (3 * P.γ - 2) *
      Real.sqrt (1 / (1 - P.γ))) * P.c ^ ((3 : ℝ) / 2) ∧
    D₂ P 0 = -(1 - Real.sqrt P.c) ^ 3 * (P.γ - 1) ^ 2 ∧
    D₂ P 0 < 0 ∧
    ∃ lowerL : ℝ, 0 < lowerL ∧ D₂ P lowerL = 0 ∧
      (∀ l : ℝ, lowerL < l → 0 < D₂ P l) ∧
      (∀ l : ℝ, 0 < l → D₂ P l = 0 → l = lowerL) := by
  have hS' := hS
  obtain ⟨hg0, hg1, hc0, hc1⟩ := hS'
  have h1g : 0 < 1 - P.γ := by linarith
  obtain ⟨s0, s1, hs2⟩ := sqrt_facts P hS
  set v := Real.sqrt (1 - P.γ) with hv
  have hv0 : 0 < v := Real.sqrt_pos.mpr h1g
  have hv2 : v ^ 2 = 1 - P.γ := Real.sq_sqrt h1g.le
  have hv1 : v < 1 := by nlinarith
  have hu : Real.sqrt (1 / (1 - P.γ)) = 1 / v := by
    rw [Real.sqrt_div' 1 h1g.le, Real.sqrt_one]
  have hr : Real.sqrt (P.c / (1 - P.γ)) = Real.sqrt P.c / v := by
    rw [Real.sqrt_div' _ h1g.le]
  have hγ : P.γ = 1 - v ^ 2 := by linarith
  set s := Real.sqrt P.c with hs
  have hc : P.c = s ^ 2 := hs2.symm
  -- rewrite everything in terms of s and v
  have hcr : (P.c / (1 - P.γ)) ^ ((3 : ℝ) / 2) = (s / v) ^ 3 := by
    rw [rp32 (div_nonneg hc0.le h1g.le), hr]
  have hc32 : P.c ^ ((3 : ℝ) / 2) = s ^ 3 := by rw [rp32 hc0.le]
  have hA : 0 < (2 * (1 - P.γ) + (3 * P.γ - 2) * Real.sqrt (1 / (1 - P.γ))) *
      P.c ^ ((3 : ℝ) / 2) := by
    rw [hu, hc32, hγ]
    have e : (2 * (1 - (1 - v ^ 2)) + (3 * (1 - v ^ 2) - 2) * (1 / v)) =
        (1 - v) ^ 2 * (2 * v + 1) / v := by field_simp; ring
    rw [e]
    have : 0 < 1 - v := by linarith
    positivity
  have hD0 : D₂ P 0 = -(1 - s) ^ 3 * (P.γ - 1) ^ 2 := by
    unfold D₂
    rw [hc32, ← hs, hc]; ring
  have hD0neg : D₂ P 0 < 0 := by
    rw [hD0]
    have : 0 < 1 - s := by linarith
    have : 0 < (P.γ - 1) ^ 2 := by nlinarith
    have : 0 < (1 - s) ^ 3 := by positivity
    nlinarith
  refine ⟨?_, hA, hD0, hD0neg, ?_⟩
  · intro l hl
    unfold fwdBuyerClosed adHocBuyerClosed D₂
    rw [hcr, hc32, hr, hu, ← hs, hc, hγ]
    field_simp
    ring
  · -- quadratic with positive leading coefficient and negative constant term
    set A := (2 * (1 - P.γ) + (3 * P.γ - 2) * Real.sqrt (1 / (1 - P.γ))) *
        P.c ^ ((3 : ℝ) / 2) with hAdef
    set B := -3 * (P.γ - 1) ^ 2 * P.c ^ ((3 : ℝ) / 2) - 3 * s * (P.γ - 1) ^ 2
        - P.c * (P.γ - 1) * (2 * Real.sqrt (P.c / (1 - P.γ)) - 6 * P.γ + 3)
        + (P.γ - 1) ^ 2 with hBdef
    set C := (P.γ - 1) * P.c ^ ((3 : ℝ) / 2) * (P.γ - 1) + 3 * s * (P.γ - 1) ^ 2
        - 3 * P.c * (P.γ - 1) ^ 2 - (P.γ - 1) ^ 2 with hCdef
    have hq : ∀ l, D₂ P l = A * l ^ 2 + B * l + C := fun l => D2_quad P l
    have hC : C < 0 := by
      have := hq 0; simp at this; rw [← this]; exact hD0neg
    clear_value A B C
    have hdisc : 0 < B ^ 2 - 4 * A * C := by nlinarith [sq_nonneg B]
    set d := Real.sqrt (B ^ 2 - 4 * A * C) with hd
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hd2 : d ^ 2 = B ^ 2 - 4 * A * C := Real.sq_sqrt hdisc.le
    have hdB : |B| < d := by
      rw [hd, ← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_lt_sqrt (sq_nonneg _); nlinarith
    have hBd1 : -d < B := by linarith [neg_abs_le B]
    have hBd2 : B < d := by linarith [le_abs_self B]
    set l1 := (-B + d) / (2 * A) with hl1
    set l2 := (-B - d) / (2 * A) with hl2
    have hl1pos : 0 < l1 := by rw [hl1]; apply div_pos <;> linarith
    have hl2neg : l2 < 0 := by rw [hl2]; apply div_neg_of_neg_of_pos <;> linarith
    have hfact : ∀ l, D₂ P l = A * (l - l1) * (l - l2) := by
      intro l
      rw [hq, hl1, hl2]
      field_simp
      ring_nf
      rw [hd2]; ring
    refine ⟨l1, hl1pos, by rw [hfact]; ring, ?_, ?_⟩
    · intro l hl
      rw [hfact]
      have : 0 < l - l1 := by linarith
      have : 0 < l - l2 := by linarith
      positivity
    · intro l hl h0
      rw [hfact] at h0
      have : l - l2 ≠ 0 := by linarith
      have hA' : A ≠ 0 := hA.ne'
      have : l - l1 = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hA'
          · exact h'
        · exact absurd h this
      linarith

end G2GImport.Sourcing


open G2GImport.Sourcing

theorem solution (P : Params) (hS : P.Standing) (k : ℝ) (q t : ℝ → ℝ)
    (heq : IsAdHocEq P 1 k q t) :
    k = 1 - Real.sqrt (P.c / (1 - P.γ)) ∧
    EY q = (1 - P.c / (1 - P.γ)) / 2 ∧
    EY t = (1 - P.c * Real.sqrt (P.c / (1 - P.γ)) - P.γ) / 3 ∧
    adHocBuyer 1 q t =
      (2 - P.c * P.γ * Real.sqrt (P.c / (1 - P.γ)) - P.γ - P.γ ^ 2) /
        (3 * (1 - P.γ)) ∧
    adHocSupplier P k t =
      (P.c * (2 * Real.sqrt (P.c / (1 - P.γ)) - 3) + 1 - P.γ) / 3 :=
  lemma_1_pf P hS k q t heq
