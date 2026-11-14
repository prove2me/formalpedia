-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.maximal_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:51.043454+00:00
-- url     : https://prove2.me/submissions/f52a69e4-3635-4214-a260-d0d7c14359c2

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max
public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
import all Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Theorems.Thm_BCFGJPSSV26_Greedy_key_lemma

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

end Mono

/-- **Pay to open** ([BCFGJPSSV26a, Lemma D.11], for the restricted bids): without
overbidding, if some facility can be paid for, some facility is `(2, 0)`-openable. -/
theorem payToOpen (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ : ℚ} {D : Fin n → ℚ}
    (hθ : 0 < θ) (hno : NoOver P d f θ D) {i : Fin m} (h : Pay2 P d f θ D i) :
    ∃ i', Open2 P d f 0 θ D i' := by
  classical
  -- the payable facility `i'` with the least `tstar`
  have hA : (univ.filter fun i ↦ Pay2 P d f θ D i).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, h⟩⟩
  obtain ⟨i', hi'A, hmin⟩ := exists_min_image _ (fun i ↦ tstar P d f θ D i) hA
  obtain ⟨T, hT, hT', hfT⟩ := (mem_filter.1 hi'A).2
  set t := tstar P d f θ D i'
  have htT : t ≤ T := tstar_le hP hd hθ hT hfT
  have hθt : θ ≤ t := θ_le_tstar f θ D i'
  refine ⟨i', t, hθt, htT.trans hT', by simpa using le_lhs3_tstar hP hd hθ htT hfT, ?_⟩
  intro i₀
  by_contra hlt
  push Not at hlt
  rcases hθt.eq_or_lt with heq | hθt'
  · rw [← heq, lhs4_at_θ] at hlt
    exact absurd (hno i₀) (not_le.2 hlt)
  -- lowering `t` a little keeps the overbidding of `i₀` above `f`
  set ξ := lhs4 P d θ D i' t i₀ - f
  have hξ : 0 < ξ := by linarith
  have hn : (0 : ℚ) < n + 1 := by positivity
  have hξn : 0 < ξ / (n + 1) := by positivity
  set T'' := max θ (t - ξ / (n + 1))
  have hT''t : T'' < t := max_lt hθt' (by linarith)
  have hθT'' : θ ≤ T'' := le_max_left _ _
  have hT''p : T'' ≤ P.θplus θ := hT''t.le.trans (htT.trans hT')
  have h1 : t - T'' ≤ ξ / (n + 1) := by
    have := le_max_right θ (t - ξ / (n + 1))
    linarith
  have h2 : (n : ℚ) * (t - T'') < ξ := by
    calc (n : ℚ) * (t - T'') ≤ n * (ξ / (n + 1)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
      _ < ξ := by
          rw [← mul_div_assoc, div_lt_iff₀ hn]
          nlinarith
  have hlip := lhs4_sub_le (P := P) (d := d) (θ := θ) (D := D) (i := i') (i₀ := i₀) hT''t.le
  -- so `i₀` is payable at `T'' < t` by the key lemma, against the choice of `i'`
  have hkl := key_lemma hP hd hθ hθT'' hT''p D i' i₀
  have hf3 : f ≤ lhs3 P d θ D i₀ T'' := by linarith [hkl.1, hkl.2]
  have h3 := tstar_le hP hd hθ hθT'' hf3
  have h4 := hmin i₀ (mem_filter.2 ⟨mem_univ _, ⟨T'', hθT'', hT''p, hf3⟩⟩)
  linarith

/-- **Maximality transfers** to smaller profiles and larger opening costs, without
overbidding (the maximality part of [BCFGJPSSV26a, Claim D.12], via [BCFGJPSSV26a, Lemmas D.10
and D.11]). -/
theorem maximal_transfer (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) (b : Bool) {f f' θ : ℚ}
    {D D' : Fin n → ℚ} (hθ : 0 < θ) (hno : NoOver P d f θ D) (hD : D' ≤ D) (hf : f ≤ f')
    (hmax : ∀ i, ¬ OpenT P d b f 0 θ D i) : ∀ i, ¬ OpenT P d b f' 0 θ D' i := by
  intro i hi
  cases b
  · obtain ⟨T, hT, hT', h3, -⟩ := (hi : Open2 P d f' 0 θ D' i)
    have hmono := lhs3_mono_D (θ := θ) (T := T) (i := i) (d := d) hP hD
    obtain ⟨i', hi'⟩ := payToOpen hP hd hθ hno (i := i) ⟨T, hT, hT', by simp at h3; linarith⟩
    exact hmax i' hi'
  · have hmono := lhs1_mono (θ := θ) (i := i) (d := d) hP hD
    refine hmax i (show Open1 P d f 0 θ D i from ?_)
    have hi' : Open1 P d f' 0 θ D' i := hi
    simp only [Open1, mul_zero, sub_zero] at hi' ⊢
    linarith

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.maximal_transfer := @BCFGJPSSV26.Greedy.maximal_transfer
