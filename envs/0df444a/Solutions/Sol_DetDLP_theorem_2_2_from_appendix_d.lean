-- Prove2me | solution 1 for DetDLP.theorem_2_2_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:45:00.205941+00:00
-- url     : https://prove2.me/submissions/e83ac106-2890-4fb6-b8dd-95fa24d7dad7

import Theorems.Thm_DetDLP_lemma_5_2_from_appendix_d

set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

private noncomputable def d1rho (x : ℝ) := max 1 ⌊Real.logb 2 (x / (⌈x ^ ((9:ℝ)/10)⌉₊ : ℝ))⌋₊

private theorem d1rho_bound {x : ℝ} (hx : 2 ≤ x) : logSafe x ≤ 30 * (d1rho x : ℝ) := by
  let y := x ^ ((9:ℝ)/10)
  have hy : 1 ≤ y := Real.one_le_rpow (by linarith) (by norm_num)
  have hp : 0 < x := by linarith
  have hq := Nat.le_ceil y
  have hq0 : 0 < (⌈y⌉₊ : ℝ) := by linarith
  have hl := Real.logb_le_logb_of_le (b:=2) (by norm_num) hq0
    (show (⌈y⌉₊ : ℝ) ≤ 2*y by linarith [Nat.ceil_lt_add_one (show 0 ≤ y by linarith)])
  rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at hl
  change Real.logb 2 (⌈y⌉₊ : ℝ) ≤ 1 + Real.logb 2 (x ^ ((9:ℝ)/10)) at hl
  rw [Real.logb_rpow_eq_mul_logb_of_pos hp] at hl
  have hf := Nat.lt_floor_add_one (Real.logb 2 (x / (⌈y⌉₊ : ℝ)))
  have hm : (⌊Real.logb 2 (x / (⌈y⌉₊ : ℝ))⌋₊ : ℝ) ≤ d1rho x := by exact_mod_cast le_max_right _ _
  have h1 : (1:ℝ) ≤ d1rho x := by exact_mod_cast (le_max_left 1 _)
  rw [Real.logb_div hp.ne' hq0.ne'] at hf hm
  unfold logSafe
  rw [max_eq_right hx]
  exact max_le (by linarith) (by linarith)

private theorem d1entry_bound {x : ℝ} (hx : 2 ≤ x) :
    x ^ ((9:ℝ)/10) * Real.sqrt (logSafe x) ≤ 4*x := by
  have hp : 0 < x := by linarith
  have hg : 1 ≤ x ^ ((1:ℝ)/5) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog := Real.log_le_rpow_div hp.le (by norm_num : (0:ℝ) < 1/5)
  have hs : logSafe x ≤ 16*x^((1:ℝ)/5) := by
    unfold logSafe
    rw [max_eq_right hx]
    apply max_le (by linarith)
    unfold Real.logb
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.log_two_gt_d9.le) (show 0 ≤ x ^ ((1:ℝ)/5) by positivity)]
  have hrt : Real.sqrt (logSafe x) ≤ 4*x^((1:ℝ)/10) := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, ← Real.rpow_mul_natCast hp.le]
    norm_num
    exact hs
  calc x ^ ((9:ℝ)/10) * Real.sqrt (logSafe x) ≤ x ^ ((9:ℝ)/10) * (4*x^((1:ℝ)/10)) := by gcongr
    _ = 4*x := by
      rw [mul_left_comm, ← Real.rpow_add hp]
      norm_num

private theorem d1mono {M : PrimitiveMachine} {o : Fin M.tapeCount} {i w : List Bool} {t s t' s' : ℝ}
    (h : RunsWithin M o i w t s) (ht : t ≤ t') (hs : s ≤ s') : RunsWithin M o i w t' s' := by
  obtain ⟨a,b,c,d,e,f,g⟩ := h
  exact ⟨a,b,c,d,e,f.trans ht,fun k v hk hv => (g k v hk hv).trans hs⟩

private theorem d1poly {k K n : ℕ} (h : k ≤ K) : polyBound k n ≤ polyBound K n := by
  unfold polyBound
  gcongr
  exact_mod_cast (show (1:ℕ) ≤ n + 1 by omega)

theorem solution (hOAI : OpenAIAppendixDPremise) :
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length)) := by
  intro C A c0 hC _ h0 E o
  obtain ⟨M, out, k, hk⟩ := lemma_5_2_from_appendix_d hOAI C c0 hC h0 E o
  let K := 6*k+4*A+c0+1
  refine ⟨M,out,K,?_⟩
  intro s P l desc G T hs he hv hd hp hP hl hL heval
  let n := s+desc.length
  let x : ℝ := s
  let r := d1rho x
  let L := Real.sqrt (logSafe x)
  let R := Real.sqrt (r : ℝ)
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast hs
  have hxn : 0 ≤ x := by linarith
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ s + desc.length by omega)
  have hg : 1 ≤ logSafe x := le_max_left _ _
  have hLpos : 0 < L := Real.sqrt_pos.mpr (by linarith)
  have hr : (1:ℝ) ≤ r := by exact_mod_cast (le_max_left 1 _)
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hLr : L ≤ 6*R := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
    have hsq : R ^ 2 = r := Real.sq_sqrt (by positivity)
    nlinarith [d1rho_bound hx, show (r:ℝ) = d1rho x by rfl]
  let y := x ^ ((9:ℝ)/10)
  let t := (n:ℝ)^c0 * (2:ℝ)^((A:ℝ)*y)
  have ht : 1 ≤ t := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (Real.one_le_rpow (by norm_num) (by dsimp [y]; positivity))
  have hf : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  obtain ⟨w,hw,hM⟩ := hk s P l ⌊t⌋₊ desc G T hs hf he hv hp hP hl hL (by
    intro v a
    obtain ⟨z,hz,b,c,h1,h2,h3,h4,h5⟩ := heval v a
    change (b:ℝ) ≤ t at h4
    have hh : b ≤ ⌊t⌋₊ := Nat.le_floor h4
    exact ⟨z,hz,b,c,h1,h2,h3,Nat.cast_le.mpr hh,h5⟩)
  simp only [max_eq_right hd] at hM
  change RunsWithin _ _ _ _ (polyBound k n * (⌊t⌋₊:ℝ) * (2:ℝ)^((k:ℝ)*x/R)) (polyBound k n) at hM
  have hkK : k ≤ K := by dsimp [K]; omega
  refine ⟨w,hw,d1mono hM ?_ (d1poly hkK)⟩
  have hex1 : (A:ℝ)*y ≤ (4*A:ℝ)*x/L := by
    apply (le_div_iff₀ hLpos).mpr
    have hh : y * L ≤ 4*x := d1entry_bound hx
    nlinarith [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) A)]
  have hex2 : (k:ℝ)*x/R ≤ (6*k:ℝ)*x/L := by
    apply (div_le_div_iff₀ hRpos hLpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLr (show 0 ≤ (k:ℝ)*x by positivity)]
  have hex : (A:ℝ)*y + (k:ℝ)*x/R ≤ (K:ℝ)*x/L := by
    apply (le_div_iff₀ hLpos).mpr
    have h1 := (le_div_iff₀ hLpos).mp hex1
    have h2 := (le_div_iff₀ hLpos).mp hex2
    dsimp [K]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) c0) hxn]
  have hpol : polyBound k n * (n:ℝ)^c0 ≤ polyBound K n := by
    unfold polyBound
    calc (k:ℝ) * ((n:ℝ)+1)^k * (n:ℝ)^c0 ≤ (k:ℝ) * ((n:ℝ)+1)^k * ((n:ℝ)+1)^c0 := by gcongr; linarith
      _ = (k:ℝ) * ((n:ℝ)+1)^(k+c0) := by rw [pow_add]; ring
      _ ≤ (K:ℝ) * ((n:ℝ)+1)^K := mul_le_mul (by exact_mod_cast hkK) (pow_le_pow_right₀ (by linarith) (by dsimp [K]; omega)) (by positivity) (by positivity)
  change _ ≤ polyBound K n * (2:ℝ)^((K:ℝ)*x/L)
  calc polyBound k n * (⌊t⌋₊:ℝ) * (2:ℝ)^((k:ℝ)*x/R) ≤ polyBound k n * t * (2:ℝ)^((k:ℝ)*x/R) := by
         have hpoly0 : 0 ≤ polyBound k n := by unfold polyBound; positivity
         gcongr
         exact Nat.floor_le (by linarith)
    _ = (polyBound k n * (n:ℝ)^c0) * (2:ℝ)^((A:ℝ)*y+(k:ℝ)*x/R) := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]; dsimp [t]; ring
    _ ≤ _ := mul_le_mul hpol (Real.rpow_le_rpow_of_exponent_le (by norm_num) hex) (by positivity) (by unfold polyBound; positivity)


