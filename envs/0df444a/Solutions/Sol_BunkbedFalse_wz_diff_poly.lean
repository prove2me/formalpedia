-- Prove2me | solution 1 for BunkbedFalse.wz_diff_poly
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T17:02:30.376088+00:00
-- url     : https://prove2.me/submissions/e6b99d86-901b-40a9-abee-a032137b5398

import Theorems.Thm_BunkbedTM_profile_indicator
import Theorems.Thm_BunkbedTM_transfer_eval
import Theorems.Thm_BunkbedTM_delta_contract
import Theorems.Thm_BunkbedTM_class_products

/-!
# The Wierman--Ziff difference polynomial for Hollom's hypergraph

Section 3 of Gladkov--Pak--Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) e2420725122.

`wzProb` is a sum over `5 ^ 12 = 244,140,625` state configurations, so it cannot be enumerated.
The proof is a transfer-matrix argument assembled from four published steps.

* `BunkbedTM.profile_indicator` — the two levels are independent, and whether `0` on level `0`
  reaches `9` on level `l` depends on the two configurations only through the partitions they
  induce on the five special vertices `{0,1,6,8,9}`.
* `BunkbedTM.transfer_eval` — sweeping the six hyperedges along the path `ρ` of Eq. [5] collapses
  `5 ^ 6` level configurations onto the `47` reachable profiles, with explicit degree-6 weights.
  Applied twice, once per level, this turns the configuration sum into a `47 × 47` profile sum.
* `BunkbedTM.delta_contract` — the levels interact only through the posts over `T = {1,6,8}`, so
  the `47 × 47` sum contracts onto 15 class products.
* `BunkbedTM.class_products` — those 15 products are `wzDiffPoly`.

All that remains here is the bookkeeping that unrolls a level sum into six nested sums (`nested`)
and applies the transfer matrix to each level in turn (`collapse`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

namespace BunkbedWZD

/-- `(Fin 6 → WZ)` as a sixfold product. -/
private def vec6 : (WZ × WZ × WZ × WZ × WZ × WZ) ≃ (Fin 6 → WZ) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2]
  invFun c := (c 0, c 1, c 2, c 3, c 4, c 5)
  left_inv p := rfl
  right_inv c := by funext i; fin_cases i <;> rfl

private lemma vec6_apply (p : WZ × WZ × WZ × WZ × WZ × WZ) :
    (vec6 p : Fin 6 → WZ)
      = ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2] := rfl

/-- `prof`, i.e. `fold 6`, written out as six `step`s. -/
private lemma prof_eq (c : Fin 6 → WZ) :
    prof c
      = step 5 (c 5) (step 4 (c 4) (step 3 (c 3)
          (step 2 (c 2) (step 1 (c 1) (step 0 (c 0) stInit))))) := rfl

/-- A sum over level configurations, unrolled into six nested sums over the six hyperedges. -/
private theorem nested (P : WZ → ℚ) (g : St → ℚ) :
    (∑ c : Fin 6 → WZ, g (prof c) * ∏ i, P (c i))
      = ∑ t₀ : WZ, ∑ t₁ : WZ, ∑ t₂ : WZ, ∑ t₃ : WZ, ∑ t₄ : WZ, ∑ t₅ : WZ,
          (P t₀ * P t₁ * P t₂ * P t₃ * P t₄ * P t₅)
            * g (step 5 t₅ (step 4 t₄ (step 3 t₃ (step 2 t₂ (step 1 t₁ (step 0 t₀ stInit)))))) := by
  rw [← Equiv.sum_comp vec6]
  rw [show (fun p : WZ × WZ × WZ × WZ × WZ × WZ => g (prof (vec6 p)) * ∏ i, P (vec6 p i))
        = (fun p : WZ × WZ × WZ × WZ × WZ × WZ =>
            (P p.1 * P p.2.1 * P p.2.2.1 * P p.2.2.2.1 * P p.2.2.2.2.1 * P p.2.2.2.2.2)
              * g (step 5 p.2.2.2.2.2 (step 4 p.2.2.2.2.1 (step 3 p.2.2.2.1
                  (step 2 p.2.2.1 (step 1 p.2.1 (step 0 p.1 stInit))))))) from ?_]
  · simp only [Fintype.sum_prod_type]
  · funext p
    rw [vec6_apply, prof_eq, Fin.prod_univ_six]
    exact mul_comm _ _

/-- The glued-connectivity indicator difference, as a function of the two profiles. -/
def dl (r₀ r₁ : St) : ℚ :=
  (if glueConn r₀ r₁ 1 then (1 : ℚ) else 0) - (if glueConn r₀ r₁ 0 then (1 : ℚ) else 0)

/-- One level collapsed by the transfer matrix. -/
private theorem collapse (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b) (g : St → St → ℚ) (s₀ : St) :
    (∑ c : Fin 6 → WZ, g s₀ (prof c) * ∏ i, P (c i))
      = ∑ m : Fin 47, g s₀ (stFinal m)
          * wFinal m (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) := by
  have h1 : (∑ c : Fin 6 → WZ, g s₀ (prof c) * ∏ i, P (c i)) = _ := nested P (fun s => g s₀ s)
  rw [h1]
  have h2 : _ = ∑ m : Fin 47,
      wFinal m (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) * g s₀ (stFinal m) :=
    BunkbedTM.transfer_eval P hsym (fun s => g s₀ s)
  rw [h2]
  exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)

end BunkbedWZD

open BunkbedWZD in
/-- **The Wierman--Ziff difference polynomial.** In the symmetric case `P_ab|c = P_ac|b`, the
difference between the cross-level and the same-level connection probability on Hollom's
hypergraph is the explicit degree-12 polynomial `wzDiffPoly`. -/
theorem solution (P : WZ → ℚ) (hsym : P .ab_c = P .ac_b) :
    wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2))
      - wzProb hollomTriple hollomT P ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2))
      = wzDiffPoly (P .abc) (P .a_b_c) (P .a_bc) (P .ab_c) := by
  rw [BunkbedTM.profile_indicator P]
  -- factor the level-0 weight out of each inner sum and collapse level 1
  have step1 : ∀ c₀ : Fin 6 → WZ,
      (∑ c₁ : Fin 6 → WZ,
          ((if glueConn (prof c₀) (prof c₁) 1 then (1 : ℚ) else 0)
            - (if glueConn (prof c₀) (prof c₁) 0 then (1 : ℚ) else 0))
            * ((∏ i, P (c₀ i)) * (∏ i, P (c₁ i))))
      = (fun s₀ => ∑ m : Fin 47, dl s₀ (stFinal m)
            * wFinal m (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c)) (prof c₀)
          * ∏ i, P (c₀ i) := by
    intro c₀
    have e : ∀ c₁ : Fin 6 → WZ,
        (((if glueConn (prof c₀) (prof c₁) 1 then (1 : ℚ) else 0)
            - (if glueConn (prof c₀) (prof c₁) 0 then (1 : ℚ) else 0))
              * ((∏ i, P (c₀ i)) * (∏ i, P (c₁ i))))
          = (dl (prof c₀) (prof c₁) * ∏ i, P (c₁ i)) * ∏ i, P (c₀ i) := by
      intro c₁; rw [dl]; ring
    rw [Finset.sum_congr rfl (fun c₁ _ => e c₁), ← Finset.sum_mul]
    exact congrArg (fun w => w * ∏ i, P (c₀ i)) (collapse P hsym dl (prof c₀))
  rw [Finset.sum_congr rfl (fun c₀ _ => step1 c₀)]
  -- collapse level 0
  have step2 : _ = ∑ j : Fin 47,
      (fun s₀ => ∑ m : Fin 47, dl s₀ (stFinal m)
          * wFinal m (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c)) (stFinal j)
        * wFinal j (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c) :=
    collapse P hsym (fun _ s₀ => ∑ m : Fin 47, dl s₀ (stFinal m)
      * wFinal m (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c)) stInit
  rw [step2]
  rw [Finset.sum_congr rfl (fun j _ => mul_comm _
    (wFinal j (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c)))]
  simp only [dl]
  rw [BunkbedTM.delta_contract, BunkbedTM.class_products]

#print axioms solution
