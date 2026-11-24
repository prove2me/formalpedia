-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:09.648226+00:00
-- url     : https://prove2.me/submissions/9d4e36e6-f721-4f8b-9210-e84926e212de

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
private theorem derivation_natCast_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m : ℕ) (x : S) : D ((m : S) * x) = (m : S) * D x := by
  have h1 : ((m : S) * x) = m • x := by rw [nsmul_eq_mul]
  have h2 : ((m : S) * D x) = m • D x := by rw [nsmul_eq_mul]
  rw [h1, h2, map_nsmul]
private theorem iterate_derivation_natCast_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m c : ℕ) (x : S) :
    (⇑D)^[m] ((c : S) * x) = (c : S) * (⇑D)^[m] x := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, derivation_natCast_mul]
private theorem iterate_derivation_sum {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (m : ℕ) {ι : Type*} (s : Finset ι) (F : ι → S) :
    (⇑D)^[m] (∑ i ∈ s, F i) = ∑ i ∈ s, (⇑D)^[m] (F i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_sum]
private theorem sum_choose_succ_mul_eq {S : Type*} [CommRing S] (u v : ℕ → S) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = ∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)) := by
  have e1 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e2 : (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e3 : (∑ i ∈ Finset.range (n + 1 + 1), (((n + 1).choose i : ℕ) : S) * (u i * v (n + 1 - i)))
      = (∑ i ∈ Finset.range (n + 1), (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u 0 * v (n + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have e4 : (∑ i ∈ Finset.range (n + 1),
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
        + u (n + 1) * v 0 := by
    rw [Finset.sum_range_succ]
    simp
  have e5 : (∑ i ∈ Finset.range n,
        (((n + 1).choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i)))
      = (∑ i ∈ Finset.range n, ((n.choose i : ℕ) : S) * (u (i + 1) * v (n - i)))
        + (∑ i ∈ Finset.range n, ((n.choose (i + 1) : ℕ) : S) * (u (i + 1) * v (n - i))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : ((n + 1).choose (i + 1) : ℕ) = n.choose i + n.choose (i + 1) :=
      Nat.choose_succ_succ n i
    rw [hc]
    push_cast
    ring
  rw [e1, e2, e3, e4, e5]
  ring
private theorem iterate_derivation_mul {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    (D : Derivation B S S) (n : ℕ) (x y : S) :
    (⇑D)^[n] (x * y)
      = ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : ∀ i ∈ Finset.range (n + 1),
          D (((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n - i] y))
            = ((n.choose i : ℕ) : S) * ((⇑D)^[i + 1] x * (⇑D)^[n - i] y)
              + ((n.choose i : ℕ) : S) * ((⇑D)^[i] x * (⇑D)^[n + 1 - i] y) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have e1 : D ((⇑D)^[i] x) = (⇑D)^[i + 1] x := (Function.iterate_succ_apply' (⇑D) i x).symm
        have e2 : D ((⇑D)^[n - i] y) = (⇑D)^[n + 1 - i] y := by
          have hni : n + 1 - i = n - i + 1 := by omega
          rw [hni]
          exact (Function.iterate_succ_apply' (⇑D) (n - i) y).symm
        rw [derivation_natCast_mul, D.leibniz, e1, e2]
        simp only [smul_eq_mul]
        ring
      rw [Function.iterate_succ_apply', ih, map_sum]
      refine Eq.trans (Finset.sum_congr rfl hstep) ?_
      rw [Finset.sum_add_distrib]
      exact sum_choose_succ_mul_eq (fun i => (⇑D)^[i] x) (fun i => (⇑D)^[i] y) n
private theorem multiIndexDeriv_succ {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
    {m : ℕ} (D : Fin (m + 1) → Derivation B S S) (α : Fin (m + 1) → ℕ) (x : S) :
    multiIndexDeriv D α x
      = (⇑(D 0))^[α 0] (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ) x) := by
  simp only [multiIndexDeriv, Fin.foldr_succ]
private theorem sum_piFinset_succ {M : Type*} [AddCommMonoid M] {m : ℕ}
    (s : Fin (m + 1) → Finset ℕ) (F : (Fin (m + 1) → ℕ) → M) :
    ∑ β ∈ Fintype.piFinset s, F β
      = ∑ j ∈ s 0, ∑ γ ∈ Fintype.piFinset (fun i => s i.succ), F (Fin.cons j γ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_equiv (finSuccFunEquivProd m) ?_ ?_
  · intro β
    constructor
    · intro hβ
      have hβ' := Fintype.mem_piFinset.1 hβ
      exact Finset.mem_product.2 ⟨hβ' 0, Fintype.mem_piFinset.2 (fun i => hβ' i.succ)⟩
    · intro hβ
      have h1 := Finset.mem_product.1 hβ
      refine Fintype.mem_piFinset.2 (fun i => ?_)
      refine Fin.cases ?_ ?_ i
      · exact h1.1
      · intro j
        exact Fintype.mem_piFinset.1 h1.2 j
  · intro β _
    exact congrArg F (fin_cons_self_tail β).symm
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D α (f * g) =
      ∑ β ∈ Fintype.piFinset fun i => Finset.range (α i + 1),
        ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g := by
  induction h with
  | zero =>
      have hset : (Fintype.piFinset fun i : Fin 0 => Finset.range (α i + 1))
          = {fun _ => 0} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
        · exact Fintype.mem_piFinset.2 (fun i => i.elim0)
        · intro x _
          funext i
          exact i.elim0
      rw [hset, Finset.sum_singleton]
      simp
  | succ h ih =>
      have hcons : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (Fin.cons j γ) x
            = (⇑(D 0))^[j] (multiIndexDeriv (fun i => D i.succ) γ x) := by
        intro j γ x
        rw [multiIndexDeriv_succ D (Fin.cons j γ) x]
        simp
      have hcons2 : ∀ (j : ℕ) (γ : Fin h → ℕ) (x : R),
          multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x
            = (⇑(D 0))^[α 0 - j]
                (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) x) := by
        intro j γ x
        rw [multiIndexDeriv_succ D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) x]
        simp
      have key : ∀ γ : Fin h → ℕ,
          (⇑(D 0))^[α 0] (((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g)
            = ∑ j ∈ Finset.range (α 0 + 1),
                ((∏ i, (α i).choose ((Fin.cons j γ : Fin (h + 1) → ℕ) i) : ℕ) : R)
                  * multiIndexDeriv D (Fin.cons j γ) f
                  * multiIndexDeriv D (fun i => α i - (Fin.cons j γ : Fin (h + 1) → ℕ) i) g := by
        intro γ
        have hA : ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * multiIndexDeriv (fun i => D i.succ) γ f
              * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g
            = ((∏ i, (α i.succ).choose (γ i) : ℕ) : R)
              * (multiIndexDeriv (fun i => D i.succ) γ f
                * multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ - γ i) g) :=
          mul_assoc _ _ _
        rw [hA, iterate_derivation_natCast_mul, iterate_derivation_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hcons j γ f, hcons2 j γ g, Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        push_cast
        ring
      rw [multiIndexDeriv_succ D α (f * g), ih (fun i => D i.succ) (fun i => α i.succ),
        iterate_derivation_sum]
      refine Eq.trans (Finset.sum_congr rfl (fun γ _ => key γ)) ?_
      rw [Finset.sum_comm]
      exact (sum_piFinset_succ (fun i : Fin (h + 1) => Finset.range (α i + 1))
        (fun β => ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g)).symm
end FunctorialResolution.EmbeddedResolution
