-- Prove2me | solution 1 for CalibeatBandit.eq_C_3
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T12:42:13.984692+00:00
-- url     : https://prove2.me/submissions/cf21e94c-ee78-444f-bfbd-fc2dcea3a63b

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf

set_option autoImplicit false

open Matrix
open scoped BigOperators

open CalibeatBandit

/-- **(C.3): the mixing step** (§C.2, proof of Lemma C.3, pp.33–34). Let `M^SR`, `M^Rec` be
column-stochastic, `λ ∈ [0, 1]`, `x ∈ Δ(𝒜)` a solution of (3.1)
`(I − λM^SR) x = (1 − λ) M^Rec e_J`, `η > 0` and `v` any real vector, and let
`H^SR = (1/η) ∑_i log(∑_j m^SR_i(j) exp(η x(i) v(j)))`, `H^Rec = (1/η) log(∑_j m^Rec_J(j) exp(η v(j)))`.
Then
`λ exp(ηH^SR) + (1 − λ) exp(ηH^Rec) ≤ ∑_j (λ(M^SR x)(j) + (1 − λ)(M^Rec e_J)(j)) exp(ηv(j))
  = ∑_j x(j) exp(ηv(j))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.3), p.34 (the claim stated on p.33).

**Formalization Note.** The printed middle term has `(M^Rec_t)(j)`; the line above it on p.34
derives the bound with `(M^Rec_t e_{J_t})(j)`, which is what is stated. The paper states the
claim for the algorithm's round-`t` quantities; it is stated here for all inputs satisfying the
hypotheses its proof uses. `m^a_i(j)` is the matrix entry `M j i`. -/
theorem solution {K : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam0 : 0 ≤ lam) (_hlam1 : lam ≤ 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) (x v : Fin K → ℝ) (hx : IsProbVec x)
    (hfix : (1 - lam • MSR) *ᵥ x = (1 - lam) • (MRec *ᵥ Pi.single J 1)) :
    lam * Real.exp (η * HSRof η MSR x v) + (1 - lam) * Real.exp (η * HRecOf η MRec J v)
        ≤ ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j)
            * Real.exp (η * v j) ∧
    ∑ j, (lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j) * Real.exp (η * v j)
        = ∑ j, x j * Real.exp (η * v j) := by
  have logArg_pos (p : Fin K → ℝ) (hp : IsProbVec p) (a : ℝ) :
      0 < ∑ j, p j * Real.exp (a * v j) := by
    have hsome : ∃ j, 0 < p j := by
      by_contra! h
      have hsum : ∑ j, p j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hp.1 j)
      linarith [hp.2]
    obtain ⟨j, hj⟩ := hsome
    exact (mul_pos hj (Real.exp_pos _)).trans_le
      (Finset.single_le_sum (fun k _ => mul_nonneg (hp.1 k) (Real.exp_nonneg _)) (Finset.mem_univ j))
  let z : Fin K → ℝ := fun i => ∑ j, MSR j i * Real.exp (η * v j)
  have hz (i : Fin K) : 0 < z i := logArg_pos _ (hSR i) η
  have hxone (i : Fin K) : x i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans_eq hx.2
  have hpow (i : Fin K) :
      (∑ j, MSR j i * Real.exp (η * x i * v j)) ≤ z i ^ x i := by
    have h := (Real.concaveOn_rpow (hx.1 i) (hxone i)).le_map_sum
      (t := Finset.univ) (w := fun j => MSR j i) (p := fun j => Real.exp (η * v j))
      (fun j _ => (hSR i).1 j) (hSR i).2
      (fun j _ => show Real.exp (η * v j) ∈ Set.Ici 0 from Real.exp_nonneg _)
    simpa only [smul_eq_mul, ← Real.exp_mul, show ∀ j, η * v j * x i = η * x i * v j by
      intro j; ring, z] using h
  have hSR_exp : Real.exp (η * HSRof η MSR x v) ≤
      ∑ j, (MSR *ᵥ x) j * Real.exp (η * v j) := by
    unfold HSRof
    rw [show η * (1 / η * ∑ i, Real.log (∑ j, MSR j i * Real.exp (η * x i * v j))) =
        ∑ i, Real.log (∑ j, MSR j i * Real.exp (η * x i * v j)) by field_simp]
    rw [Real.exp_sum]
    simp_rw [Real.exp_log (logArg_pos _ (hSR _) _)]
    calc
      _ ≤ ∏ i, z i ^ x i :=
        Finset.prod_le_prod (fun i _ => (logArg_pos _ (hSR i) _).le) (fun i _ => hpow i)
      _ ≤ ∑ i, x i * z i :=
        Real.geom_mean_le_arith_mean_weighted Finset.univ x z (fun i _ => hx.1 i) hx.2
          (fun i _ => (hz i).le)
      _ = _ := by
        simp only [z, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hRec_exp : Real.exp (η * HRecOf η MRec J v) =
      ∑ j, (MRec *ᵥ Pi.single J 1) j * Real.exp (η * v j) := by
    unfold HRecOf
    rw [show η * (1 / η * Real.log (∑ j, MRec j J * Real.exp (η * v j))) =
        Real.log (∑ j, MRec j J * Real.exp (η * v j)) by field_simp]
    rw [Real.exp_log (logArg_pos _ (hRec J) η), mulVec_single_one]
    rfl
  constructor
  · rw [hRec_exp]
    refine (add_le_add_left (mul_le_mul_of_nonneg_left hSR_exp hlam0) _).trans_eq ?_
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [sub_mulVec, one_mulVec, smul_mulVec] at hfix
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrFun hfix j
    change x j - lam * (MSR *ᵥ x) j = (1 - lam) * (MRec *ᵥ Pi.single J 1) j at h
    rw [show lam * (MSR *ᵥ x) j + (1 - lam) * (MRec *ᵥ Pi.single J 1) j = x j by linarith]

