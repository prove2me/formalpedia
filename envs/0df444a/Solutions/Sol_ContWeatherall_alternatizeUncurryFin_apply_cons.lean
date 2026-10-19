-- Prove2me | solution 1 for ContWeatherall.alternatizeUncurryFin_apply_cons
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:43:58.850177+00:00
-- url     : https://prove2.me/submissions/a69f3296-c82b-4f4b-af6d-bae1de2697cb

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

theorem removeNth_succ_cons_aux {E : Type*} {n : ℕ} (i : Fin (n + 1)) (x : E)
    (v : Fin (n + 1) → E) :
    Fin.removeNth i.succ (Fin.cons x v : Fin (n + 2) → E) = Fin.cons x (i.removeNth v) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem auc_main {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (L : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin L (Fin.cons x v) =
      L x v - ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • L (v i) (Fin.cons x (i.removeNth v)) := by
  rw [alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
    Fin.cons_succ, removeNth_succ_cons_aux, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end ContWeatherall

theorem solution {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (L : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin L (Fin.cons x v) =
      L x v - ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • L (v i) (Fin.cons x (i.removeNth v)) :=
  ContWeatherall.auc_main L x v
