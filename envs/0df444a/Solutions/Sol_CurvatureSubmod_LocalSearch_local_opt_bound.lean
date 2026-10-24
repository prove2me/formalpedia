-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.local_opt_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T06:23:58.543695+00:00
-- url     : https://prove2.me/submissions/2e7eb286-418f-4c48-9157-cf6e759a5234

import Mathlib
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting
/-
Complete consequence of Equation5.4, 23 October2026.
Original mathematics: Sviridenko, Vondrak and Ward, arXiv:1311.4728v2, p.7;
Filmus and Ward, arXiv:1204.4526v4, Theorem1 and Lemmas1,6-8.
The earlier local reduction is included under PreviousReduction with its exact
mathematical body and original accepted Brualdi proof/credit retained.
Local-reduction source SHA256 a147be0da0dd22061286fb3c91aa04d769ca258ec43ee2a419f57aaabe645f58.
The full Equation5.4 proof follows with solution renamed potential_bound;
source SHA256 1162c528751516216d614b80cba38e6da1c02e64f9b6a51f7f8f08c322e4e71d,
submission8b0b5c44-ec85-4a3d-96c9-dd884e70f58b. The final theorem discharges
the formerly explicit potential premise. No open theorem is imported.
Alexander Richard Towell directed the campaign; OpenAI Codex constructed and
verified the proofs and composition. No novelty or independent human review
claimed. Lean/Mathlib and platform credit is retained in the included bodies.
-/
namespace PreviousReduction
/-
Conditional local-search reduction, 23 October 2026.
The Filmus-Ward potential inequality remains an explicit premise; this file
is not a proof of any open platform target. Equation (5.5), the signed linear
exchange cancellation, is proved without a potential premise. The accepted
Brualdi proof is included with its original credit below. Original source:
Sviridenko, Vondrak and Ward arXiv:1311.4728v2, printed p.7. Alexander Richard
Towell directed the work; OpenAI Codex constructed and checked these proofs.
No novelty or independent human review is asserted.
-/

open scoped BigOperators
open CurvatureSubmod.LocalSearch
set_option autoImplicit false

namespace LocalSearchReduction

variable {X : Type} [Fintype X] [DecidableEq X]

lemma exchange_fixed (M : Matroid X) (A : Finset X) (hA : M.IsBase (A : Set X))
    (a b : X) (ha : a ∈ A) (hb : b ∈ A)
    (hs : M.IsBase (↑(insert b (A.erase a)) : Set X)) : b = a := by
  have he : (↑(insert b (A.erase a)) : Set X) = A :=
    hs.eq_of_subset_isBase hA (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hb
      · exact Finset.mem_of_mem_erase hx)
  have ham : a ∈ insert b (A.erase a) := by
    change a ∈ (↑(insert b (A.erase a)) : Set X)
    rw [he]; exact ha
  exact (by simpa using ham : a = b).symm

lemma linear_exchange (w : X → ℝ) (M : Matroid X) (A : Finset X)
    (hA : M.IsBase (A : Set X)) (a b : X) (ha : a ∈ A)
    (hs : M.IsBase (↑(insert b (A.erase a)) : Set X)) :
    linFun w A - linFun w (insert b (A.erase a)) = w a - w b := by
  by_cases hb : b ∈ A
  · have he := exchange_fixed M A hA a b ha hb hs
    subst b
    simp [Finset.insert_erase ha]
  · have hbe : b ∉ A.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    have he := Finset.sum_erase_add A w ha
    simp only [linFun, Finset.sum_insert hbe]
    linarith

lemma linear_cancellation (w : X → ℝ) (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (A : Set X)) (π : X → X)
    (hπ : Set.BijOn π (A : Set X) (B : Set X))
    (hs : ∀ a ∈ A, M.IsBase (↑(insert (π a) (A.erase a)) : Set X)) :
    ∑ a ∈ A, (linFun w A - linFun w (insert (π a) (A.erase a))) =
      linFun w A - linFun w B := by
  have hsum : ∑ a ∈ A, w (π a) = ∑ b ∈ B, w b := by
    apply Finset.sum_bij (fun a _ => π a)
    · exact fun a ha => hπ.mapsTo ha
    · exact fun a ha b hb he => hπ.injOn ha hb he
    · intro b hb
      obtain ⟨a,ha,he⟩ := hπ.surjOn hb
      exact ⟨a,ha,he⟩
    · intros; rfl
  calc
    _ = ∑ a ∈ A, (w a - w (π a)) := by
      apply Finset.sum_congr rfl
      exact fun a ha => linear_exchange w M A hA a (π a) ha (hs a ha)
    _ = linFun w A - linFun w B := by rw [Finset.sum_sub_distrib, hsum]; rfl

lemma potential_comparison (g : Finset X → ℝ) (w : X → ℝ)
    (M : Matroid X) (A B : Finset X) (hA : M.IsBase (A : Set X))
    (π : X → X) (hπ : Set.BijOn π (A : Set X) (B : Set X))
    (hs : ∀ a ∈ A, M.IsBase (↑(insert (π a) (A.erase a)) : Set X))
    (hpotential : g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g A) :
    (1 - Real.exp (-1)) * g B + linFun w B +
      ∑ a ∈ A, (psi g w A - psi g w (insert (π a) (A.erase a)))
      ≤ g A + linFun w A := by
  have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr (show (0:ℝ) < 1 by norm_num)
  have hc : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.mpr (show (-1:ℝ) ≤ 0 by norm_num)
    linarith
  have hid : (1 - Real.exp (-1)) * (Real.exp 1 / (Real.exp 1 - 1)) = 1 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt (sub_pos.mpr he)]
  have hh := mul_le_mul_of_nonneg_left hpotential hc
  rw [← mul_assoc, hid, one_mul] at hh
  have hlin := linear_cancellation w M A B hA π hπ hs
  have hsum : (∑ a ∈ A, (psi g w A - psi g w (insert (π a) (A.erase a)))) =
      (1 - Real.exp (-1)) * (∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a))))
      + (linFun w A - linFun w B) := by
    rw [← hlin, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros
    simp only [psi]
    ring
  rw [hsum]
  nlinarith

end LocalSearchReduction

#print axioms LocalSearchReduction.linear_cancellation
#print axioms LocalSearchReduction.potential_comparison

/-
Brualdi's bijective base exchange, 23 October 2026.
Original mathematical attribution: Richard A. Brualdi (1969), as cited in
Sviridenko, Vondrak and Ward, arXiv:1311.4728v2, Lemma 5.1, printed p.6.
The pinned v2 PDF and its Brualdi reference were inspected; the original 1969
paper was not inspected. The v2 PDF displays a 2019 title date despite the
2014 arXiv version date. No new mathematical discovery is claimed.
New formalization: Hall's condition follows from spanning by fundamental
circuit neighbors and matroid rank. A matching between equal-sized bases is
inverted to give the required exchange bijection, including common elements.
Alexander Richard Towell directed the work; OpenAI Codex substantially
constructed and verified the proof. mikedeng1 supplied the formal target;
Shuze Chen confirmed its statement, not this proof. Mathlib contributors
supply Hall's theorem and the matroid foundations. No prior platform proof
is reused and no independent human review is claimed.
-/
namespace AcceptedExchange

open Set Matroid
open scoped Classical
set_option autoImplicit false

namespace ExchangeResearch

lemma mem_closure_neighbors {X : Type*} (M : Matroid X) (A : Set X)
    (hA : M.IsBase A) (b : X) (hb : b ∈ M.E) :
    b ∈ M.closure (M.fundCircuit b A ∩ A) := by
  by_cases hbA : b ∈ A
  · exact M.subset_closure _ (inter_subset_right.trans hA.subset_ground)
      ⟨M.mem_fundCircuit b A,hbA⟩
  · have hc := hA.fundCircuit_isCircuit hb hbA
    apply M.closure_subset_closure (X := M.fundCircuit b A \ {b}) _
      (hc.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit b A))
    intro z hz
    refine ⟨hz.1,?_⟩
    rcases M.fundCircuit_subset_insert b A hz.1 with he | hzA
    · exact False.elim (hz.2 he)
    · exact hzA

lemma neighbor_exchange {X : Type*} [DecidableEq X] (M : Matroid X) (A : Finset X)
    (hA : M.IsBase (A : Set X)) (b x : X) (hb : b ∈ M.E) (hx : x ∈ A)
    (hxc : x ∈ M.fundCircuit b (A : Set X)) :
    M.IsBase (↑(insert b (A.erase x)) : Set X) := by
  by_cases hbA : b ∈ (A : Set X)
  · have he : x=b := by simpa [M.fundCircuit_eq_of_mem hbA] using hxc
    subst x
    simpa only [Finset.insert_erase hbA] using hA
  · have hc : b ∈ M.closure (A : Set X) := by rw [hA.closure_eq]; exact hb
    have hi := (hA.indep.mem_fundCircuit_iff hc hbA).mp hxc
    have he := hA.exchange_isBase_of_indep' hx hbA hi
    have hbx : b ≠ x := by intro h; subst b; exact hbA hx
    rw [← Set.insert_sdiff_singleton_comm hbx] at he
    simpa only [Finset.coe_insert,Finset.coe_erase] using he

lemma hall_condition {X : Type} [Fintype X] [DecidableEq X] (M : Matroid X)
    (A B : Finset X) (hA : M.IsBase (A : Set X)) (hB : M.IsBase (B : Set X)) :
    ∀ s : Finset {b // b ∈ B}, s.card ≤
      (s.biUnion (fun b => (Finset.univ : Finset {a // a ∈ A}).filter
        (fun a => a.val ∈ M.fundCircuit b.val (A : Set X)))).card := by
  classical
  intro s
  let t : {b // b ∈ B} → Finset {a // a ∈ A} := fun b => Finset.univ.filter
    (fun a => a.val ∈ M.fundCircuit b.val (A : Set X))
  let C : Finset X := s.image Subtype.val
  let D : Finset X := (s.biUnion t).image Subtype.val
  have hC : M.Indep (C : Set X) := by
    apply hB.indep.subset
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact b.property
  have hspan : (C : Set X) ⊆ M.closure (D : Set X) := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    apply M.closure_subset_closure _ (mem_closure_neighbors M (A : Set X) hA b.val
      (hB.subset_ground b.property))
    intro a ha
    apply Finset.mem_image.mpr
    refine ⟨⟨a,ha.2⟩,?_,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨b,hb,by simp [t,ha.1]⟩
  have hr : (C : Set X).encard ≤ (D : Set X).encard := by
    calc
      (C : Set X).encard ≤ M.eRk (M.closure (D : Set X)) := hC.encard_le_eRk_of_subset hspan
      _ = M.eRk (D : Set X) := M.eRk_closure_eq _
      _ ≤ (D : Set X).encard := M.eRk_le_encard _
  have hCcard : C.card = s.card := Finset.card_image_iff.mpr
    (fun a _ b _ h => Subtype.ext h)
  have hDcard : D.card = (s.biUnion t).card := Finset.card_image_iff.mpr
    (fun a _ b _ h => Subtype.ext h)
  have hcard : C.card ≤ D.card := by exact_mod_cast hr
  rw [hCcard,hDcard] at hcard
  exact hcard

end ExchangeResearch

theorem solution {X : Type} [Fintype X] [DecidableEq X] (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X)) :
    ∃ π : X → X, Set.BijOn π (↑A : Set X) (↑B : Set X) ∧
      ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X) := by
  classical
  let t : {b // b ∈ B} → Finset {a // a ∈ A} := fun b => Finset.univ.filter
    (fun a => a.val ∈ M.fundCircuit b.val (A : Set X))
  obtain ⟨f,hfinj,hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp
    (ExchangeResearch.hall_condition M A B hA hB)
  have hc : Fintype.card {b // b ∈ B} = Fintype.card {a // a ∈ A} := by
    simpa using hB.ncard_eq_ncard_of_isBase hA
  have hfbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj,hc⟩
  let e : {b // b ∈ B} ≃ {a // a ∈ A} := Equiv.ofBijective f hfbij
  let π : X → X := fun x => if hx : x ∈ A then (e.symm ⟨x,hx⟩).val else x
  have hp : ∀ x (hx : x ∈ A), π x = (e.symm ⟨x,hx⟩).val := by
    intro x hx; simp [π,hx]
  refine ⟨π,⟨?_,?_,?_⟩,?_⟩
  · intro x hx
    rw [hp x hx]
    exact (e.symm ⟨x,hx⟩).property
  · intro x hx y hy h
    rw [hp x hx,hp y hy] at h
    have hh := e.symm.injective (Subtype.ext h)
    exact congrArg Subtype.val hh
  · intro b hb
    refine ⟨(e ⟨b,hb⟩).val,(e ⟨b,hb⟩).property,?_⟩
    rw [hp _ (e ⟨b,hb⟩).property]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨b,hb⟩)
  · intro x hx
    rw [hp x hx]
    apply ExchangeResearch.neighbor_exchange M A hA _ x
      (hB.subset_ground (e.symm ⟨x,hx⟩).property) hx
    have hh := hfmem (e.symm ⟨x,hx⟩)
    have he : f (e.symm ⟨x,hx⟩) = ⟨x,hx⟩ := e.apply_symm_apply ⟨x,hx⟩
    simpa [t,he] using hh
#print axioms solution

end AcceptedExchange

namespace LocalSearchReduction

theorem local_opt_from_potential {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (w : X → ℝ) (M : Matroid X) (S O : Finset X)
    (hS : IsSwapLocalOpt M (psi g w) S) (hO : M.IsBase (O : Set X))
    (hpotential : ∀ π : X → X, Set.BijOn π (S : Set X) (O : Set X) →
      (∀ a ∈ S, M.IsBase (↑(insert (π a) (S.erase a)) : Set X)) →
      g O + ∑ a ∈ S, (hPot g S - hPot g (insert (π a) (S.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g S) :
    (1 - Real.exp (-1)) * g O + linFun w O ≤ g S + linFun w S := by
  obtain ⟨π,hπ,hs⟩ := AcceptedExchange.solution M S O hS.1 hO
  have hc := potential_comparison g w M S O hS.1 π hπ hs (hpotential π hπ hs)
  have hnonneg : 0 ≤ ∑ a ∈ S, (psi g w S - psi g w (insert (π a) (S.erase a))) := by
    apply Finset.sum_nonneg
    intro a ha
    by_cases hb : π a ∈ S
    · have he := exchange_fixed M S hS.1 a (π a) ha hb (hs a ha)
      simp [he,Finset.insert_erase ha]
    · exact sub_nonneg.mpr (hS.2 a ha (π a) hb (hs a ha))
  linarith

end LocalSearchReduction

#print axioms LocalSearchReduction.local_opt_from_potential

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (w : X → ℝ) (M : Matroid X) (S O : Finset X)
    (hS : IsSwapLocalOpt M (psi g w) S) (hO : M.IsBase (O : Set X))
    (hpotential : ∀ π : X → X, Set.BijOn π (S : Set X) (O : Set X) →
      (∀ a ∈ S, M.IsBase (↑(insert (π a) (S.erase a)) : Set X)) →
      g O + ∑ a ∈ S, (hPot g S - hPot g (insert (π a) (S.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g S) :
    (1 - Real.exp (-1)) * g O + linFun w O ≤ g S + linFun w S :=
  LocalSearchReduction.local_opt_from_potential g w M S O hS hO hpotential
#print axioms solution

end PreviousReduction
/-
Complete Filmus-Ward exchange-potential inequality, 23 October 2026.
Original mathematics: Yuval Filmus and Justin Ward, Monotone Submodular
Maximization over a Matroid via Non-Oblivious Local Search, arXiv:1204.4526v4
(upload19November2013; manuscript20November2013), Theorem1 and Lemmas1,6-8,
pp.8,11-13, specialized to curvature one. Journal DOI10.1137/130920277.
PDF SHA256 e7b1b8d63c7522835ac75fa71c8f0e2c0462cb7d6dfcaef801b6a0d1b8bc49bb.
The platform target is Equation(5.4), p.7, of Maxim Sviridenko, Jan Vondrak and
Justin Ward, Optimal approximation for submodular and supermodular optimization
with bounded curvature, SODA2015 version9October2014.
mikedeng1 supplied the platform statement and definitions. This proof retains
our earlier checked coefficient and normalization body, with its former solution
renamed previous_potential_support. The new part proves the exact potential
marginal formula, expectation monotonicity, exchange and coverage bounds, and
the finite deletion identity. Normalization restores g(empty)>=0; no hidden
zero-empty-set assumption remains. The supplied bijection is used as a
hypothesis, so our separate accepted Brualdi proof is not imported here.
Lean/Mathlib contributors supply finite sums, calculus and matroid foundations.
Alexander Richard Towell directed the campaign and verification requirements;
OpenAI Codex constructed, integrated and checked this proof. No mathematical
novelty or independent human proof review is claimed.
-/

/-
Integral coefficients for the non-oblivious potential, specializing Filmus and
Ward, SIAM J. Comput. 43 (2014), DOI 10.1137/130920277, to curvature one.
Formalization by Alexander Richard Towell (queelius), with substantial OpenAI
Codex assistance. These coefficient and normalization lemmas are reused below in the full Equation5.4 proof.
-/
open MeasureTheory
noncomputable section
namespace PotentialCoefficients

def kernel (k j : ℕ) (p : ℝ) : ℝ :=
  Real.exp p / (Real.exp 1 - 1) * p ^ k * (1 - p) ^ j

def weight (k j : ℕ) : ℝ := ∫ p in (0 : ℝ)..1, kernel k j p

theorem denom_pos : 0 < Real.exp 1 - 1 := by
  have h : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  linarith

theorem kernel_continuous (k j : ℕ) : Continuous (kernel k j) := by
  unfold kernel
  fun_prop

theorem kernel_integrable (k j : ℕ) :
    IntervalIntegrable (kernel k j) volume (0 : ℝ) 1 :=
  (kernel_continuous k j).intervalIntegrable _ _

theorem weight_nonneg (k j : ℕ) : 0 ≤ weight k j := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro p hp
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos p).le denom_pos.le)
    (pow_nonneg hp.1 k)) (pow_nonneg (sub_nonneg.mpr hp.2) j)

theorem weight_zero_zero : weight 0 0 = 1 := by
  simp only [weight, kernel, pow_zero, mul_one]
  rw [intervalIntegral.integral_div]
  simp only [integral_exp, Real.exp_zero]
  exact div_self (ne_of_gt denom_pos)

theorem weight_pascal (k j : ℕ) : weight k j = weight (k + 1) j + weight k (j + 1) := by
  rw [weight, weight, weight, ← intervalIntegral.integral_add (kernel_integrable _ _)
    (kernel_integrable _ _)]
  apply intervalIntegral.integral_congr
  intro p _
  simp only [kernel, pow_succ]
  ring

theorem kernel_derivative (k j : ℕ) (p : ℝ) :
    HasDerivAt (kernel k j)
      (kernel k j p + (k : ℝ) * kernel (k - 1) j p - (j : ℝ) * kernel k (j - 1) p) p := by
  have h := (((Real.hasDerivAt_exp p).div_const (Real.exp 1 - 1)).mul
    ((hasDerivAt_id p).pow k)).mul
    (((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)).pow j)
  exact h.congr_deriv (by dsimp [kernel]; ring)

theorem weight_recurrence (k j : ℕ) :
    weight k j + (k : ℝ) * weight (k - 1) j - (j : ℝ) * weight k (j - 1) =
    (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
    (if k = 0 then 1 / (Real.exp 1 - 1) else 0) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun p _ => kernel_derivative k j p)
    (((kernel_integrable k j).add ((kernel_integrable (k-1) j).const_mul (k : ℝ))).sub
      ((kernel_integrable k (j-1)).const_mul (j : ℝ)))
  rw [intervalIntegral.integral_sub ((kernel_integrable k j).add
    ((kernel_integrable (k-1) j).const_mul (k : ℝ)))
    ((kernel_integrable k (j-1)).const_mul (j : ℝ)),
    intervalIntegral.integral_add (kernel_integrable k j)
      ((kernel_integrable (k-1) j).const_mul (k : ℝ)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  change weight k j + (k : ℝ) * weight (k-1) j - (j : ℝ) * weight k (j-1) = _ at h
  rw [h]
  by_cases hk : k = 0 <;> by_cases hj : j = 0 <;> simp [kernel, hk, hj]

end PotentialCoefficients

namespace PotentialNormalization
open CurvatureSubmod.LocalSearch PotentialCoefficients
variable {X : Type} [Fintype X] [DecidableEq X]

theorem hPot_one_card (A : Finset X) :
    hPot (fun _ : Finset X => (1 : ℝ)) A =
      ∑ k ∈ Finset.range (A.card + 1), (A.card.choose k : ℝ) *
        (if k = 0 then 0 else weight (k - 1) (A.card - k)) := by
  unfold hPot
  rw [Finset.sum_filter]
  trans ∑ B ∈ A.powerset, if B.card = 0 then 0 else weight (B.card - 1) (A.card - B.card)
  · apply Finset.sum_congr rfl
    intro B _
    by_cases hB : B.Nonempty
    · have hcard : B.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hB)
      simp [hB, hcard, weight, kernel]
    · have hcard : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB)
      simp [hB, hcard]
  · rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_powersetCard k A (fun i => if i = 0 then (0 : ℝ) else weight (i-1) (A.card-i))]
    simp [nsmul_eq_mul]

theorem hPot_one_eq_of_card_eq (A B : Finset X) (h : A.card = B.card) :
    hPot (fun _ : Finset X => (1 : ℝ)) A = hPot (fun _ : Finset X => (1 : ℝ)) B := by
  rw [hPot_one_card, hPot_one_card, h]

theorem hPot_sub_const (g : Finset X → ℝ) (c : ℝ) (A : Finset X) :
    hPot (fun B => g B - c) A = hPot g A - c * hPot (fun _ => 1) A := by
  simp only [hPot, sub_mul, Finset.sum_sub_distrib, one_mul, Finset.mul_sum]

theorem hPot_shift_difference (g : Finset X → ℝ) (c : ℝ)
    (A B : Finset X) (h : A.card = B.card) :
    hPot (fun C => g C - c) A - hPot (fun C => g C - c) B = hPot g A - hPot g B := by
  rw [hPot_sub_const, hPot_sub_const, hPot_one_eq_of_card_eq A B h]
  ring

theorem normalized_properties (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) :
    (∀ A, 0 ≤ g A - g ∅) ∧ (g ∅ - g ∅ = 0) ∧
    MonoInc (fun A => g A - g ∅) ∧
    NonmonotoneSubmod.Shared.Submodular (fun A => g A - g ∅) := by
  refine ⟨?_, sub_self _, ?_, ?_⟩
  · intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert a A ha ih =>
      have h := hm A a
      unfold marg at h
      linarith
  · intro A a
    have h := hm A a
    unfold marg at h ⊢
    linarith
  · intro A B
    have h := hs A B
    linarith

theorem normalization_transfer (g : Finset X → ℝ) (hzero : 0 ≤ g ∅)
    (A B : Finset X) (T : X → Finset X) (hcard : ∀ a ∈ A, A.card = (T a).card)
    (hbound : (g B - g ∅) + ∑ a ∈ A,
      (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a)) ≤
      Real.exp 1 / (Real.exp 1 - 1) * (g A - g ∅)) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (T a)) ≤
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hsum : (∑ a ∈ A,
      (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a))) =
      ∑ a ∈ A, (hPot g A - hPot g (T a)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hPot_shift_difference g (g ∅) A (T a) (hcard a ha)
  rw [hsum] at hbound
  have hfactor : (1 : ℝ) ≤ Real.exp 1 / (Real.exp 1 - 1) := by
    apply (le_div_iff₀ denom_pos).mpr
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hzero]

theorem coefficient_balance (g : Finset X → ℝ) (A : Finset X) :
    (∑ B ∈ A.powerset, g B *
      (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1))) =
      Real.exp 1 / (Real.exp 1 - 1) * g A - 1 / (Real.exp 1 - 1) * g ∅ := by
  trans ∑ B ∈ A.powerset,
    ((if B = A then Real.exp 1 / (Real.exp 1 - 1) * g A else 0) -
      (if B = ∅ then 1 / (Real.exp 1 - 1) * g ∅ else 0))
  · apply Finset.sum_congr rfl
    intro B hB
    have hsub : B ⊆ A := Finset.mem_powerset.mp hB
    have hcard : A.card - B.card = 0 ↔ B = A := by
      constructor
      · intro h
        exact Finset.eq_of_subset_of_card_le hsub (Nat.sub_eq_zero_iff_le.mp h)
      · rintro rfl
        simp
    rw [weight_recurrence]
    simp only [hcard, Finset.card_eq_zero]
    split_ifs <;> simp_all <;> ring
  · rw [Finset.sum_sub_distrib]
    simp

end PotentialNormalization

theorem coefficient_identities :
    (∀ k j : ℕ, 0 ≤ PotentialCoefficients.weight k j) ∧
    PotentialCoefficients.weight 0 0 = 1 ∧
    (∀ k j : ℕ, PotentialCoefficients.weight k j =
      PotentialCoefficients.weight (k+1) j + PotentialCoefficients.weight k (j+1)) ∧
    (∀ k j : ℕ, PotentialCoefficients.weight k j +
      (k : ℝ) * PotentialCoefficients.weight (k-1) j -
      (j : ℝ) * PotentialCoefficients.weight k (j-1) =
      (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
      (if k = 0 then 1 / (Real.exp 1 - 1) else 0)) :=
  ⟨PotentialCoefficients.weight_nonneg, PotentialCoefficients.weight_zero_zero,
    PotentialCoefficients.weight_pascal, PotentialCoefficients.weight_recurrence⟩



open CurvatureSubmod.LocalSearch PotentialCoefficients

theorem previous_potential_support {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (A : Finset X) :
    (∀ k j : ℕ, 0 ≤ weight k j) ∧
    weight 0 0 = 1 ∧
    (∀ k j : ℕ, weight k j = weight (k+1) j + weight k (j+1)) ∧
    (∀ k j : ℕ, weight k j + (k : ℝ) * weight (k-1) j - (j : ℝ) * weight k (j-1) =
      (if j = 0 then Real.exp 1 / (Real.exp 1 - 1) else 0) -
      (if k = 0 then 1 / (Real.exp 1 - 1) else 0)) ∧
    ((∑ B ∈ A.powerset, g B *
      (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1))) =
      Real.exp 1 / (Real.exp 1 - 1) * g A - 1 / (Real.exp 1 - 1) * g ∅) ∧
    (∀ (c : ℝ) (B : Finset X), A.card = B.card →
      hPot (fun C => g C - c) A - hPot (fun C => g C - c) B = hPot g A - hPot g B) ∧
    (MonoInc g → NonmonotoneSubmod.Shared.Submodular g →
      (∀ B, 0 ≤ g B - g ∅) ∧ (g ∅ - g ∅ = 0) ∧
      MonoInc (fun B => g B - g ∅) ∧
      NonmonotoneSubmod.Shared.Submodular (fun B => g B - g ∅)) ∧
    (∀ (B : Finset X) (T : X → Finset X), 0 ≤ g ∅ →
      (∀ a ∈ A, A.card = (T a).card) →
      ((g B - g ∅) + ∑ a ∈ A,
        (hPot (fun C => g C - g ∅) A - hPot (fun C => g C - g ∅) (T a)) ≤
        Real.exp 1 / (Real.exp 1 - 1) * (g A - g ∅)) →
      g B + ∑ a ∈ A, (hPot g A - hPot g (T a)) ≤
        Real.exp 1 / (Real.exp 1 - 1) * g A) := by
  refine ⟨weight_nonneg, weight_zero_zero, weight_pascal, weight_recurrence,
    PotentialNormalization.coefficient_balance g A, ?_, ?_, ?_⟩
  · intro c B h
    exact PotentialNormalization.hPot_shift_difference g c A B h
  · exact PotentialNormalization.normalized_properties g
  · intro B T hzero hcard hbound
    exact PotentialNormalization.normalization_transfer g hzero A B T hcard hbound

-- Dropping the lower endpoint term is already false for the empty-set coefficient.
theorem endpoint_control : weight 0 0 ≠ Real.exp 1 / (Real.exp 1 - 1) := by
  rw [weight_zero_zero]
  apply ne_of_lt
  apply (lt_div_iff₀ denom_pos).mpr
  linarith

#print axioms previous_potential_support
#print axioms endpoint_control

/- Further marginal representation, 23 October 2026. The preceding coefficient
and normalization proof is retained from our checked turn3 packet, SHA256
c0726137cae5c2854202215241a9c5f73c813e8ade8b583f699cbfc65a0d3104.
Source: Filmus and Ward, arXiv:1204.4526v4, Lemma1 and the exchange argument.
The following lemmas complete Equation5.4 without an open theorem dependency. -/
namespace PotentialMarginals
open CurvatureSubmod.LocalSearch PotentialCoefficients
variable {X : Type} [Fintype X] [DecidableEq X]

theorem hPot_sum (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    hPot g A = ∑ B ∈ A.powerset, g B * weight (B.card-1) (A.card-B.card) := by
  unfold hPot
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hn : B.Nonempty
  · simp [hn, weight, kernel]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    subst B
    simp [hg]

theorem marginal_representation (g : Finset X → ℝ) (hg : g ∅ = 0)
    (A : Finset X) (a : X) (ha : a ∉ A) :
    hPot g (insert a A) - hPot g A =
      ∑ B ∈ A.powerset, weight B.card (A.card-B.card) * (g (insert a B) - g B) := by
  rw [hPot_sum g hg, hPot_sum g hg, Finset.sum_powerset_insert ha,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hBA := Finset.mem_powerset.mp hB
  have hcard := Finset.card_le_card hBA
  have hab : a ∉ B := fun h => ha (hBA h)
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hab]
  have hsub : A.card + 1 - B.card = (A.card-B.card)+1 := by omega
  have hsub2 : A.card + 1 - (B.card+1) = A.card-B.card := by omega
  rw [hsub, hsub2, Nat.add_sub_cancel]
  by_cases hz : B = ∅
  · subst B
    simp [hg, mul_comm]
  · have hb : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have hpas := weight_pascal (B.card-1) (A.card-B.card)
    rw [Nat.sub_add_cancel hb] at hpas
    rw [hpas]
    ring

noncomputable def expect (A : Finset X) (f : Finset X → ℝ) : ℝ :=
  ∑ B ∈ A.powerset, weight B.card (A.card-B.card) * f B

theorem expect_insert (A : Finset X) (a : X) (ha : a ∉ A) (f : Finset X → ℝ) :
    expect (insert a A) f = ∑ B ∈ A.powerset,
      (weight B.card (A.card-B.card+1) * f B +
        weight (B.card+1) (A.card-B.card) * f (insert a B)) := by
  unfold expect
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  have hBA := Finset.mem_powerset.mp hB
  have hcard := Finset.card_le_card hBA
  have hab : a ∉ B := fun h => ha (hBA h)
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hab]
  congr 3 <;> omega

theorem expect_const (A : Finset X) (c : ℝ) : expect A (fun _ => c) = c := by
  induction A using Finset.induction_on with
  | empty => simp [expect,weight_zero_zero]
  | @insert a A ha ih =>
    rw [expect_insert A a ha]
    calc
      _ = expect A (fun _ => c) := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [← add_mul, add_comm, ← weight_pascal]
      _ = c := ih

theorem expect_insert_le (A : Finset X) (a : X) (ha : a ∉ A) (f : Finset X → ℝ)
    (hf : ∀ B ⊆ A, f (insert a B) ≤ f B) : expect (insert a A) f ≤ expect A f := by
  rw [expect_insert A a ha]
  apply Finset.sum_le_sum
  intro B hB
  have hm := mul_le_mul_of_nonneg_left (hf B (Finset.mem_powerset.mp hB))
    (weight_nonneg (B.card+1) (A.card-B.card))
  have hp := weight_pascal B.card (A.card-B.card)
  rw [hp, add_mul]
  linarith

theorem marg_antitone (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X) (hAB : A ⊆ B) (b : X) :
    marg g B b ≤ marg g A b := by
  by_cases hb : b ∈ B
  · simpa [marg,Finset.insert_eq_of_mem hb] using hm A b
  · have hu : insert b A ∪ B = insert b B := by ext x; simp; aesop
    have hi : insert b A ∩ B = A := by ext x; simp; aesop
    have h := hs (insert b A) B
    rw [hu,hi] at h
    unfold marg
    linarith

theorem expect_marg_insert_le (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (a b : X) (ha : a ∉ A) :
    expect (insert a A) (fun B => marg g B b) ≤ expect A (fun B => marg g B b) := by
  apply expect_insert_le A a ha
  intro B hB
  exact marg_antitone g hm hs B (insert a B) (Finset.subset_insert _ _) b


theorem swap_comparison (g : Finset X → ℝ) (hg : g ∅ = 0) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (a b : X)
    (ha : a ∈ A) (hb : b ∉ A.erase a) :
    hPot g A - hPot g (insert b (A.erase a)) ≤
      (hPot g A - hPot g (A.erase a)) - expect A (fun B => marg g B b) := by
  have h := expect_marg_insert_le g hm hs (A.erase a) a b (Finset.notMem_erase _ _)
  rw [Finset.insert_erase ha] at h
  have hr := marginal_representation g hg (A.erase a) b hb
  change hPot g (insert b (A.erase a)) - hPot g (A.erase a) =
    expect (A.erase a) (fun B => marg g B b) at hr
  linarith

theorem monoInc_monotone (g : Finset X → ℝ) (hm : MonoInc g) : Monotone g := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro A a ha
  exact sub_nonneg.mp (hm A a)

theorem union_marginal_bound (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (T B : Finset X) :
    g (T ∪ B) ≤ g T + ∑ b ∈ B, marg g T b := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b B hb ih =>
    rw [Finset.sum_insert hb, Finset.union_insert]
    have h := marg_antitone g hm hs T (T ∪ B) Finset.subset_union_left b
    simp only [marg] at h ih ⊢
    linarith

theorem marginal_sum_bound (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (T B : Finset X) :
    g B - g T ≤ ∑ b ∈ B, marg g T b := by
  have h := union_marginal_bound g hm hs T B
  have hmono := monoInc_monotone g hm (show B ⊆ T ∪ B from Finset.subset_union_right)
  linarith

theorem expected_marginal_sum (g : Finset X → ℝ) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X) :
    g B - expect A g ≤ ∑ b ∈ B, expect A (fun T => marg g T b) := by
  have h : expect A (fun T => g B - g T) ≤
      expect A (fun T => ∑ b ∈ B, marg g T b) := by
    apply Finset.sum_le_sum
    intro T hT
    exact mul_le_mul_of_nonneg_left (marginal_sum_bound g hm hs T B)
      (weight_nonneg T.card (A.card-T.card))
  have he : expect A (fun T => g B - g T) = g B - expect A g := by
    simp only [expect,mul_sub,Finset.sum_sub_distrib]
    rw [← expect, expect_const]
  have he2 : expect A (fun T => ∑ b ∈ B, marg g T b) =
      ∑ b ∈ B, expect A (fun T => marg g T b) := by
    simp only [expect,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he,he2] at h
  exact h


theorem powerset_erase (A : Finset X) (a : X) :
    (A.erase a).powerset = A.powerset.filter (fun B => a ∉ B) := by
  ext B
  simp [Finset.subset_erase, and_comm]

theorem sum_erased_potential (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    (∑ a ∈ A, hPot g (A.erase a)) =
      ∑ B ∈ A.powerset, ((A.card-B.card : ℕ) : ℝ) *
        (g B * weight (B.card-1) (A.card-1-B.card)) := by
  calc
    _ = ∑ a ∈ A, ∑ B ∈ A.powerset,
        if a ∉ B then g B * weight (B.card-1) (A.card-1-B.card) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hPot_sum g hg, powerset_erase, Finset.sum_filter, Finset.card_erase_of_mem ha]
    _ = ∑ B ∈ A.powerset, ∑ a ∈ A,
        if a ∉ B then g B * weight (B.card-1) (A.card-1-B.card) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      have hBA := Finset.mem_powerset.mp hB
      rw [← Finset.sum_filter]
      have hf : A.filter (fun a => a ∉ B) = A \ B := by ext a; simp
      rw [hf, Finset.sum_const, Finset.card_sdiff_of_subset hBA]
      simp [nsmul_eq_mul]


theorem deletion_identity (g : Finset X → ℝ) (hg : g ∅ = 0) (A : Finset X) :
    (∑ a ∈ A, (hPot g A - hPot g (A.erase a))) + expect A g =
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,sum_erased_potential g hg,
    hPot_sum g hg,Finset.mul_sum]
  unfold expect
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ B ∈ A.powerset, g B *
        (weight B.card (A.card-B.card) + (B.card : ℝ) * weight (B.card-1) (A.card-B.card) -
        ((A.card-B.card : ℕ) : ℝ) * weight B.card (A.card-B.card-1)) := by
      apply Finset.sum_congr rfl
      intro B hB
      have hcard := Finset.card_le_card (Finset.mem_powerset.mp hB)
      by_cases hzero : B = ∅
      · subst B; simp [hg]
      by_cases heq : B = A
      · subst B; simp; ring
      have hb : 1 ≤ B.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
      have hlt : B.card < A.card := lt_of_le_of_ne hcard (by
        intro hc
        exact heq (Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hB) hc.ge))
      have hj : 1 ≤ A.card-B.card := by omega
      have hs : A.card-1-B.card = A.card-B.card-1 := by omega
      have hpas := weight_pascal (B.card-1) (A.card-B.card-1)
      rw [Nat.sub_add_cancel hb,Nat.sub_add_cancel hj] at hpas
      have hc : (A.card : ℝ) = (B.card : ℝ) + ((A.card-B.card : ℕ) : ℝ) := by
        exact_mod_cast (show A.card = B.card + (A.card-B.card) by omega)
      rw [hs,hpas,hc]
      ring
    _ = _ := by rw [PotentialNormalization.coefficient_balance,hg,mul_zero,sub_zero]


theorem normalized_exchange_bound (g : Finset X → ℝ) (hg : g ∅ = 0) (hm : MonoInc g)
    (hs : NonmonotoneSubmod.Shared.Submodular g) (A B : Finset X)
    (π : X → X) (hπ : Set.BijOn π (A : Set X) (B : Set X))
    (hnew : ∀ a ∈ A, π a ∉ A.erase a) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a))) ≤
      Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hsum := Finset.sum_le_sum (s := A) (fun a ha => swap_comparison g hg hm hs A a (π a) ha (hnew a ha))
  have hbij : (∑ a ∈ A, expect A (fun T => marg g T (π a))) =
      ∑ b ∈ B, expect A (fun T => marg g T b) := by
    apply Finset.sum_bij (fun a _ => π a)
    · intro a ha; exact hπ.mapsTo ha
    · intro a ha a' ha' he; exact hπ.injOn ha ha' he
    · intro b hb; obtain ⟨a,ha,he⟩ := hπ.surjOn hb; exact ⟨a,ha,he⟩
    · intro a ha; rfl
  simp only [Finset.sum_sub_distrib] at hsum
  rw [hbij] at hsum
  have hcover := expected_marginal_sum g hm hs A B
  have hdel := deletion_identity g hg A
  simp only [Finset.sum_sub_distrib] at hdel ⊢
  linarith

end PotentialMarginals
#print axioms PotentialMarginals.marginal_representation

open CurvatureSubmod.LocalSearch PotentialMarginals

theorem potential_bound {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (M : Matroid X) (A B : Finset X)
    (hA : M.IsBase (↑A : Set X)) (hB : M.IsBase (↑B : Set X))
    (π : X → X) (hπ : Set.BijOn π (↑A : Set X) (↑B : Set X))
    (hswap : ∀ x ∈ A, M.IsBase (↑(insert (π x) (A.erase x)) : Set X)) :
    g B + ∑ a ∈ A, (hPot g A - hPot g (insert (π a) (A.erase a)))
      ≤ Real.exp 1 / (Real.exp 1 - 1) * g A := by
  have hcard : ∀ a ∈ A, A.card = (insert (π a) (A.erase a)).card := by
    intro a ha
    have hc := hA.ncard_eq_ncard_of_isBase (hswap a ha)
    simpa only [Set.ncard_coe_finset] using hc
  have hnew : ∀ a ∈ A, π a ∉ A.erase a := by
    intro a ha hb
    have hc := hcard a ha
    rw [Finset.insert_eq_of_mem hb,Finset.card_erase_of_mem ha] at hc
    have hp : 0 < A.card := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  have hn := PotentialNormalization.normalized_properties g hgmono hgsub
  apply PotentialNormalization.normalization_transfer g (hg0 ∅) A B
    (fun a => insert (π a) (A.erase a)) hcard
  exact normalized_exchange_bound (fun C => g C - g ∅) hn.2.1 hn.2.2.1 hn.2.2.2 A B π hπ hnew

#print axioms potential_bound


open CurvatureSubmod.LocalSearch
theorem solution {X : Type} [Fintype X] [DecidableEq X] (g : Finset X → ℝ)
    (hg0 : ∀ A, 0 ≤ g A) (hgmono : MonoInc g) (hgsub : NonmonotoneSubmod.Shared.Submodular g)
    (w : X → ℝ) (M : Matroid X) (S : Finset X) (hS : IsSwapLocalOpt M (psi g w) S)
    (O : Finset X) (hO : M.IsBase (↑O : Set X)) :
    (1 - Real.exp (-1)) * g O + linFun w O ≤ g S + linFun w S := by
  apply PreviousReduction.LocalSearchReduction.local_opt_from_potential g w M S O hS hO
  intro π hπ hswap
  exact potential_bound g hg0 hgmono hgsub M S O hS.1 hO π hπ hswap

#print axioms solution
