-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.noOver_raise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:57:00.568286+00:00
-- url     : https://prove2.me/submissions/0a37ab59-49e1-4bbb-ad04-56792d53c863

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

/-- **Raising the time keeps no overbidding** after a maximal sequence of type 2 (the step
"increasing `θ`" of [BCFGJPSSV26a, Lemma E.6]). -/
theorem noOver_raise (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ : ℚ} {D : Fin n → ℚ}
    (hθ : 0 < θ) (hno : NoOver P d f θ D) (hmax : ∀ i, ¬ Open2 P d f 0 θ D i) :
    NoOver P d f (P.θplus θ) D := by
  intro i₀
  by_contra hlt
  push Not at hlt
  have hθp : θ ≤ P.θplus θ := by
    unfold Par.θplus
    nlinarith [sq_nonneg P.ε]
  -- the overbidding at `θ⁺` is `Ψ` at `T = θ⁺`, at most what `i₀` collects in (iii)
  have hkl := (key_lemma hP hd hθ hθp le_rfl D i₀ i₀).2
  have hover : over P d (P.θplus θ) D i₀ =
      ∑ j, bid (min (P.θplus θ) ((1 - P.δ) * D j)) (d j i₀) := rfl
  obtain ⟨i', hi'⟩ := payToOpen hP hd hθ hno (i := i₀) ⟨P.θplus θ, hθp, le_rfl, by linarith⟩
  exact hmax i' hi'

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.noOver_raise := @BCFGJPSSV26.Greedy.noOver_raise
