-- Prove2me | solution 1 for ChebNodeTelescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:27:17.361496+00:00
-- url     : https://prove2.me/submissions/ed029dbc-b6b2-4c00-9aac-3f57a956fe4d

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_ChebNodeTelescope

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) :
    ∏ a ∈ Finset.Icc 2 m,
        (1 - Polynomial.Chebyshev.node m a) /
          (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a) = 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  set h : ℝ := Real.pi / (2 * (m : ℝ)) with hhdef
  have hhpos : 0 < h := by rw [hhdef]; positivity
  have hmh : (m : ℝ) * h = Real.pi / 2 := by rw [hhdef]; field_simp
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hhle : h ≤ Real.pi / 4 := by nlinarith [Real.pi_pos]
  -- Step 0 of the .tex proof: positivity of the relevant sines, for 1 ≤ k ≤ m+1.
  have hsinpos : ∀ k : ℕ, 1 ≤ k → k ≤ m + 1 → 0 < Real.sin ((k : ℝ) * h) := by
    intro k hk1 hk2
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    have hkR : (k : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hk2
    have hle : (k : ℝ) * h ≤ ((m : ℝ) + 1) * h := by nlinarith
    nlinarith [Real.pi_pos]
  have hne : ∀ k : ℕ, 1 ≤ k → k ≤ m + 1 → Real.sin ((k : ℝ) * h) ≠ 0 :=
    fun k h1 h2 => (hsinpos k h1 h2).ne'
  -- Step 4 of the .tex proof: the telescoping, with `h` FIXED and the top index free.
  -- `m` cannot be inducted on directly: `h` depends on it.
  have telescope : ∀ M : ℕ, 2 ≤ M →
      (∀ k : ℕ, 1 ≤ k → k ≤ M + 1 → Real.sin ((k : ℝ) * h) ≠ 0) →
      ∏ a ∈ Finset.Icc 2 M,
        (Real.sin ((a : ℝ) * h) ^ 2
          / (Real.sin (((a + 1 : ℕ) : ℝ) * h) * Real.sin (((a - 1 : ℕ) : ℝ) * h)))
      = (Real.sin ((M : ℝ) * h) * Real.sin (2 * h))
          / (Real.sin (((1 : ℕ) : ℝ) * h) * Real.sin (((M + 1 : ℕ) : ℝ) * h)) := by
    intro M
    induction M with
    | zero => intro hM _; omega
    | succ b ih =>
      intro hM hneM
      rcases Nat.lt_or_ge b 2 with hb | hb
      · have hb1 : b = 1 := by omega
        subst hb1
        norm_num
        ring
      · rw [Finset.prod_Icc_succ_top (by omega),
          ih hb (fun k hk1 hk2 => hneM k hk1 (by omega))]
        have hbne : Real.sin ((b : ℝ) * h) ≠ 0 := hneM b (by omega) (by omega)
        have hb1ne : Real.sin (((b + 1 : ℕ) : ℝ) * h) ≠ 0 := hneM (b + 1) (by omega) (by omega)
        have hb2ne : Real.sin (((b + 2 : ℕ) : ℝ) * h) ≠ 0 := hneM (b + 2) (by omega) (by omega)
        have h1ne : Real.sin (((1 : ℕ) : ℝ) * h) ≠ 0 := hneM 1 (by omega) (by omega)
        have e1 : ((b + 1 + 1 : ℕ) : ℝ) = ((b + 2 : ℕ) : ℝ) := by push_cast; ring
        have e2 : ((b + 1 - 1 : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
          have hb' : b + 1 - 1 = b := by omega
          rw [hb']
        rw [e1, e2]
        field_simp
  -- Steps 1-3 of the .tex proof: rewrite every factor of the product.
  have stageB : ∀ a ∈ Finset.Icc 2 m,
      (1 - Polynomial.Chebyshev.node m a) /
          (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a)
        = Real.sin ((a : ℝ) * h) ^ 2
            / (Real.sin (((a + 1 : ℕ) : ℝ) * h) * Real.sin (((a - 1 : ℕ) : ℝ) * h)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha2, ham⟩ := ha
    have hdbl : ∀ k : ℕ, Polynomial.Chebyshev.node m k = Real.cos (2 * ((k : ℝ) * h)) := by
      intro k
      rw [Polynomial.Chebyshev.node, hhdef]
      congr 1
      field_simp
    -- eq:cnt-num
    have hnum : 1 - Polynomial.Chebyshev.node m a = 2 * Real.sin ((a : ℝ) * h) ^ 2 := by
      rw [hdbl a, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq ((a : ℝ) * h)]
    have hcastm : (((a - 1 : ℕ)) : ℝ) = (a : ℝ) - 1 := by
      have h1a : (1 : ℕ) ≤ a := by omega
      push_cast [Nat.cast_sub h1a]; ring
    -- eq:cnt-den
    have hden : Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m a
        = 2 * Real.sin (((a + 1 : ℕ) : ℝ) * h) * Real.sin (((a - 1 : ℕ) : ℝ) * h) := by
      rw [hdbl 1, hdbl a, Real.cos_sub_cos, hcastm]
      push_cast
      have e1 : (2 * ((1 : ℝ) * h) + 2 * ((a : ℝ) * h)) / 2 = ((a : ℝ) + 1) * h := by ring
      have e2 : (2 * ((1 : ℝ) * h) - 2 * ((a : ℝ) * h)) / 2 = -(((a : ℝ) - 1) * h) := by ring
      rw [e1, e2, Real.sin_neg]
      ring
    rw [hnum, hden]
    have hp1 : Real.sin (((a + 1 : ℕ) : ℝ) * h) ≠ 0 := hne (a + 1) (by omega) (by omega)
    have hp2 : Real.sin (((a - 1 : ℕ) : ℝ) * h) ≠ 0 := hne (a - 1) (by omega) (by omega)
    field_simp
  rw [Finset.prod_congr rfl stageB, telescope m hm hne]
  -- Step 5 of the .tex proof: evaluate, using m*h = pi/2.
  have hcos : 0 < Real.cos h := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hsm : Real.sin ((m : ℝ) * h) = 1 := by rw [hmh, Real.sin_pi_div_two]
  have hsm1 : Real.sin (((m + 1 : ℕ) : ℝ) * h) = Real.cos h := by
    have hc : (((m + 1 : ℕ) : ℝ)) * h = h + Real.pi / 2 := by push_cast; rw [← hmh]; ring
    rw [hc, Real.sin_add_pi_div_two]
  have hsh : Real.sin h ≠ 0 := by
    have := hsinpos 1 le_rfl (by omega); simpa using this.ne'
  rw [hsm, hsm1, Real.sin_two_mul]
  push_cast
  field_simp
