-- Prove2me | solution 1 for CondC.disc_tensor
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:44:53.211366+00:00
-- url     : https://prove2.me/submissions/62091b30-5a44-4691-8dea-046605085c4d

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

open CondC

section g72cc
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def g72cc_Z (a : ℕ → V) : Prop := ∃ N : ℕ, ∀ n ≥ N, a n = 0

theorem g72cc_Z_add (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b) :
    g72cc_Z (fun n => a n + b n) := by
  obtain ⟨N, hN⟩ := ha; obtain ⟨M, hM⟩ := hb
  exact ⟨max N M, fun n hn => by simp [hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩

theorem g72cc_Z_sub (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b) :
    g72cc_Z (fun n => a n - b n) := by
  obtain ⟨N, hN⟩ := ha; obtain ⟨M, hM⟩ := hb
  exact ⟨max N M, fun n hn => by simp [hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩

theorem g72cc_Z_smul (k : ℂ) (a : ℕ → V) (ha : g72cc_Z a) : g72cc_Z (fun n => k • a n) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, fun n hn => by simp [hN n hn]⟩

theorem g72cc_sum_eq (a : ℕ → V) (N M : ℕ) (hN : ∀ n ≥ N, a n = 0) (hM : ∀ n ≥ M, a n = 0) :
    ∑ n ∈ Finset.range N, a n = ∑ n ∈ Finset.range M, a n := by
  wlog h : N ≤ M generalizing N M
  · exact (this M N hM hN (by omega)).symm
  rw [← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (fun n hn => hN n (Finset.mem_Ico.1 hn).1), add_zero]

open Classical in
noncomputable def g72cc_int (a : ℕ → V) (h : g72cc_Z a) : V :=
  ∑ n ∈ Finset.range (Nat.find h), a n

theorem g72cc_int_eq (a : ℕ → V) (h : g72cc_Z a) (N : ℕ) (hN : ∀ n ≥ N, a n = 0) :
    g72cc_int a h = ∑ n ∈ Finset.range N, a n := by
  classical
  unfold g72cc_int
  exact g72cc_sum_eq a _ _ (Nat.find_spec h) hN

theorem g72cc_uniq (I : ∀ a : ℕ → V, g72cc_Z a → V)
    (hD : ∀ (v : V) (n : ℕ) (h : g72cc_Z (DiracV v n)), I (DiracV v n) h = v)
    (hA : ∀ (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b),
      I (fun n => a n + b n) (g72cc_Z_add a b ha hb) = I a ha + I b hb) :
    ∀ (N : ℕ) (a : ℕ → V) (hN : ∀ n ≥ N, a n = 0) (ha : g72cc_Z a),
      I a ha = ∑ n ∈ Finset.range N, a n := by
  have congrI : ∀ (a b : ℕ → V) (hab : a = b) (ha : g72cc_Z a) (hb : g72cc_Z b), I a ha = I b hb := by
    intro a b hab ha hb; subst hab; rfl
  intro N
  induction N with
  | zero =>
    intro a hN ha
    have h0 : a = 0 := funext fun n => hN n (Nat.zero_le n)
    have := hA a a ha ha
    rw [congrI (fun n => a n + a n) a (by funext n; simp [h0]) _ ha] at this
    simp only [Finset.range_zero, Finset.sum_empty]
    have : I a ha + I a ha = I a ha + 0 := by rw [← this, add_zero]
    exact add_left_cancel this
  | succ N ih =>
    intro a hN ha
    let a' : ℕ → V := fun n => if n = N then 0 else a n
    have ha' : ∀ n ≥ N, a' n = 0 := by
      intro n hn; by_cases h : n = N
      · simp [a', h]
      · simp only [a', h, if_false]; exact hN n (by omega)
    have hZ' : g72cc_Z a' := ⟨N, ha'⟩
    have hZD : g72cc_Z (DiracV (a N) N) := ⟨N + 1, fun n hn => by simp [DiracV]; omega⟩
    have hsplit : (fun n => a' n + DiracV (a N) N n) = a := by
      funext n; by_cases h : n = N
      · subst h; simp [a', DiracV]
      · simp [a', DiracV, h]
    have := hA a' (DiracV (a N) N) hZ' hZD
    rw [congrI _ a hsplit _ ha, ih a' ha' hZ', hD] at this
    rw [this, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn; have : n ≠ N := by simp at hn; omega
    simp [a', this]




noncomputable def g72cc_liq (p : ℝ) : PLiquidStructure p V where
  summable := fun _ => True
  dirac_summable := fun _ _ => trivial
  summable_add := fun _ _ _ _ => trivial
  summable_sub := fun _ _ _ _ => trivial
  summable_smul := fun _ _ _ => trivial
  nullseq := g72cc_Z
  null_add := g72cc_Z_add
  null_smul := g72cc_Z_smul
  null_eventually_zero := fun _ h => h
  integrate := g72cc_int
  integrate_dirac := by
    intro v n h
    rw [g72cc_int_eq _ h (n + 1) (fun m hm => by simp [DiracV]; omega)]
    rw [Finset.sum_eq_single n (fun m _ hm => by simp [DiracV, hm]) (fun h => by simp at h)]
    simp [DiracV]
  integrate_add := by
    intro a b ha hb
    obtain ⟨N, hN⟩ := id ha; obtain ⟨M, hM⟩ := id hb
    have hN' : ∀ n ≥ max N M, a n = 0 := fun n hn => hN n (le_of_max_le_left hn)
    have hM' : ∀ n ≥ max N M, b n = 0 := fun n hn => hM n (le_of_max_le_right hn)
    rw [g72cc_int_eq _ _ (max N M) (fun n hn => by simp [hN' n hn, hM' n hn]),
      g72cc_int_eq _ _ _ hN', g72cc_int_eq _ _ _ hM', Finset.sum_add_distrib]
  integrate_smul := by
    intro k a ha
    obtain ⟨N, hN⟩ := id ha
    rw [g72cc_int_eq _ _ N (fun n hn => by simp [hN n hn]), g72cc_int_eq _ _ _ hN, Finset.smul_sum]
  integrate_unique := by
    intro I hD hA _ a ha
    obtain ⟨N, hN⟩ := id ha
    rw [g72cc_uniq I hD hA N a hN ha, g72cc_int_eq _ _ _ hN]

end g72cc

section g72dt

def g72dt_S : Submodule ℂ (ℕ × ℕ → ℂ) where
  carrier := {f | PowerDecay2 1 f}
  add_mem' := by
    intro f g hf hg r₁ r₂ h1 h1' h2 h2' ε hε
    obtain ⟨N, hN⟩ := hf r₁ r₂ h1 h1' h2 h2' (ε / 2) (by positivity)
    obtain ⟨M, hM⟩ := hg r₁ r₂ h1 h1' h2 h2' (ε / 2) (by positivity)
    refine ⟨max N M, fun i j hi hj => ?_⟩
    have a := hN i j (le_of_max_le_left hi) (le_of_max_le_left hj)
    have b := hM i j (le_of_max_le_right hi) (le_of_max_le_right hj)
    have hp : 0 ≤ r₁ ^ i * r₂ ^ j := by positivity
    calc ‖(f + g) (i, j)‖ * r₁ ^ i * r₂ ^ j = ‖f (i, j) + g (i, j)‖ * (r₁ ^ i * r₂ ^ j) := by
          simp [mul_assoc]
      _ ≤ (‖f (i, j)‖ + ‖g (i, j)‖) * (r₁ ^ i * r₂ ^ j) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
      _ = ‖f (i, j)‖ * r₁ ^ i * r₂ ^ j + ‖g (i, j)‖ * r₁ ^ i * r₂ ^ j := by ring
      _ < ε := by linarith
  zero_mem' := by
    intro r₁ r₂ _ _ _ _ ε hε
    exact ⟨0, fun i j _ _ => by simpa using hε⟩
  smul_mem' := by
    intro c f hf r₁ r₂ h1 h1' h2 h2' ε hε
    obtain ⟨N, hN⟩ := hf r₁ r₂ h1 h1' h2 h2' (ε / (‖c‖ + 1)) (by positivity)
    refine ⟨N, fun i j hi hj => ?_⟩
    have a := hN i j hi hj
    have hp : 0 ≤ ‖f (i, j)‖ * r₁ ^ i * r₂ ^ j := by positivity
    have hc : 0 ≤ ‖c‖ := norm_nonneg c
    have : ‖f (i, j)‖ * r₁ ^ i * r₂ ^ j * (‖c‖ + 1) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at a
    calc ‖(c • f) (i, j)‖ * r₁ ^ i * r₂ ^ j = ‖c‖ * (‖f (i, j)‖ * r₁ ^ i * r₂ ^ j) := by
          simp [norm_mul]; ring
      _ ≤ (‖f (i, j)‖ * r₁ ^ i * r₂ ^ j) * (‖c‖ + 1) := by nlinarith
      _ < ε := this

abbrev g72dt_T := ↥g72dt_S

def g72dt_d : DiscAlgebraData2 1 g72dt_T where
  coeffs := fun v => v.1
  decay := fun v => v.2
  inj := fun v w h => Subtype.ext h
  surj := fun f hf => ⟨⟨f, hf⟩, rfl⟩
  coeffs_add := fun _ _ _ _ => rfl
  coeffs_zero := fun _ _ => rfl
  coeffs_smul := fun _ _ _ _ => rfl

theorem g72dt_diag (v : g72dt_T) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ i ≥ N, ‖v.1 (i, i)‖ * r ^ i < δ := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hs1 : Real.sqrt r < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hr1
  obtain ⟨N, hN⟩ := v.2 (Real.sqrt r) (Real.sqrt r) hs hs1 hs hs1 δ hδ
  refine ⟨N, fun i hi => ?_⟩
  have := hN i i hi hi
  have e : Real.sqrt r ^ i * Real.sqrt r ^ i = r ^ i := by
    rw [← mul_pow, Real.mul_self_sqrt hr.le]
  calc ‖v.1 (i, i)‖ * r ^ i = ‖v.1 (i, i)‖ * Real.sqrt r ^ i * Real.sqrt r ^ i := by
        rw [mul_assoc, e]
    _ < δ := this

def g72dt_convF (v w : g72dt_T) : g72dt_T :=
  ⟨fun ij => v.1 (ij.1, ij.1) * w.1 (ij.2, ij.2), by
    intro r₁ r₂ h1 h1' h2 h2' ε hε
    set δ := min ε 1 with hδdef
    have hδ : 0 < δ := lt_min hε one_pos
    obtain ⟨N, hN⟩ := g72dt_diag v r₁ h1 h1' δ hδ
    obtain ⟨M, hM⟩ := g72dt_diag w r₂ h2 h2' δ hδ
    refine ⟨max N M, fun i j hi hj => ?_⟩
    have a := hN i (le_of_max_le_left hi)
    have b := hM j (le_of_max_le_right hj)
    have a0 : 0 ≤ ‖v.1 (i, i)‖ * r₁ ^ i := by positivity
    have b0 : 0 ≤ ‖w.1 (j, j)‖ * r₂ ^ j := by positivity
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδε : δ ≤ ε := min_le_left _ _
    calc ‖v.1 (i, i) * w.1 (j, j)‖ * r₁ ^ i * r₂ ^ j
        = (‖v.1 (i, i)‖ * r₁ ^ i) * (‖w.1 (j, j)‖ * r₂ ^ j) := by rw [norm_mul]; ring
      _ < δ * δ := mul_lt_mul'' a b a0 b0
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ.le
      _ ≤ ε := by linarith⟩

def g72dt_conv : g72dt_T →ₗ[ℂ] g72dt_T →ₗ[ℂ] g72dt_T :=
  LinearMap.mk₂ ℂ g72dt_convF
    (fun a b c => Subtype.ext (funext fun ij => by simp [g72dt_convF, add_mul]))
    (fun k a b => Subtype.ext (funext fun ij => by simp [g72dt_convF, mul_assoc]))
    (fun a b c => Subtype.ext (funext fun ij => by simp [g72dt_convF, mul_add]))
    (fun k a b => Subtype.ext (funext fun ij => by simp [g72dt_convF]; ring))

def g72dt_b : g72dt_T →ₗ[ℂ] g72dt_T →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun v w => v.1 (0, 1) * w.1 (0, 0))
    (fun a b c => by simp [add_mul]) (fun k a b => by simp [mul_assoc])
    (fun a b c => by simp [mul_add]) (fun k a b => by simp; ring)

def g72dt_delta (ij : ℕ × ℕ) : g72dt_T :=
  ⟨fun x => if x = ij then 1 else 0, by
    intro r₁ r₂ _ _ _ _ ε hε
    refine ⟨ij.1 + ij.2 + 1, fun i j hi _ => ?_⟩
    have : (i, j) ≠ ij := by intro h; rw [← h] at hi; simp at hi
    simp [this, hε]⟩

end g72dt

theorem solution : ¬ (∀ (p r : ℝ), 0 < p → p ≤ 1 → 0 < r →
    ∀ (V W T U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      [AddCommGroup T] [Module ℂ T] [AddCommGroup U] [Module ℂ U],
      ∀ (dV : DiscAlgebraData2 r V) (dW : DiscAlgebraData2 r W)
        (dT : DiscAlgebraData2 r T),
      ∀ (lV : PLiquidStructure p V) (lW : PLiquidStructure p W)
        (lU : PLiquidStructure p U),
      ∀ (conv : V →ₗ[ℂ] W →ₗ[ℂ] T),
      (∀ (v : V) (w : W) (i j : ℕ),
        dT.coeffs (conv v w) (i, j) = dV.coeffs v i * dW.coeffs w j) →
      IsPLiquid p T ∧
      ∀ b : V →ₗ[ℂ] W →ₗ[ℂ] U, LiquidBilinear p V W U lV lW lU b →
        ∃! L : T →ₗ[ℂ] U, ∀ (v : V) (w : W), L (conv v w) = b v w) := by
  intro h
  have hb : LiquidBilinear 1 g72dt_T g72dt_T ℂ (g72cc_liq 1) (g72cc_liq 1) (g72cc_liq 1) g72dt_b := by
    constructor
    · intro a ha w
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, fun n hn => by simp [hN n hn]⟩
    · intro a ha v
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, fun n hn => by simp [hN n hn]⟩
  obtain ⟨L, hL, -⟩ := (h 1 1 one_pos le_rfl one_pos g72dt_T g72dt_T g72dt_T ℂ g72dt_d g72dt_d g72dt_d
    (g72cc_liq 1) (g72cc_liq 1) (g72cc_liq 1) g72dt_conv (fun v w i j => rfl)).2 g72dt_b hb
  have h0 : g72dt_conv (g72dt_delta (0, 1)) (g72dt_delta (0, 0)) = 0 := by
    apply Subtype.ext; funext ij
    simp [g72dt_conv, g72dt_convF, g72dt_delta]
    omega
  have := hL (g72dt_delta (0, 1)) (g72dt_delta (0, 0))
  rw [h0, map_zero] at this
  simp [g72dt_b, g72dt_delta] at this
