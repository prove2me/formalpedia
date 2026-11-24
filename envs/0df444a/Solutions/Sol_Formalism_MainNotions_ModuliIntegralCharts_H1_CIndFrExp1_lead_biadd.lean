-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.lead_biadd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:14.550823+00:00
-- url     : https://prove2.me/submissions/e8850411-69a9-4e53-8407-aa186f14a62b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
private theorem memIo_lemma {σ : Type} (n : ℕ) (p : MvPolynomial σ S) :
    p ∈ Io S σ ^ n ↔ ∀ x ∈ p.support, n ≤ Finsupp.degree x :=
  mem_pow_idealOfVars_iff n p
private theorem ccmem_lemma_2 {σ : Type} {n : ℕ} {p : MvPolynomial σ S} (hp : p ∈ Io S σ ^ (n + 1)) :
    coeff 0 p = 0 := by
  by_contra hne
  have h := (memIo_lemma (n + 1) p).1 hp 0 (MvPolynomial.mem_support_iff.2 hne)
  simp [Finsupp.degree] at h
private theorem ccaeval_lemma_3 {σ τ : Type} (g : σ → MvPolynomial τ S) (hg : ∀ i, constantCoeff (g i) = 0)
    (p : MvPolynomial σ S) : constantCoeff (aeval g p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq, constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, constantCoeff_X, hg, mul_zero]
private theorem memcc_lemma_19 {σ : Type} {p : MvPolynomial σ S} (hp : constantCoeff p = 0) :
    p ∈ Io S σ ^ 1 := by
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  exact (MvPolynomial.mem_support_iff.1 hx) hp
private theorem weak_lemma_24 {σ : Type} {m n : ℕ} (h : m ≤ n) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ n) : p ∈ Io S σ ^ m := by
  rw [memIo_lemma] at hp ⊢
  intro x hx
  have := hp x hx
  omega
private theorem base_lemma_17 {σ τ : Type} (g g' : σ → MvPolynomial τ S)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (p : MvPolynomial σ S) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, sub_self, Submodule.zero_mem]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    have e : aeval g p * g i - aeval g' p * g' i =
        aeval g p * (g i - g' i) + (aeval g p - aeval g' p) * g' i := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hgg i)) (Ideal.mul_mem_right _ _ hp)
private theorem subst_lemma_18 {σ τ : Type} (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ ^ 1)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (n : ℕ) :
    ∀ p ∈ Io S σ ^ n, aeval g p ∈ Io S τ ^ n ∧ aeval g p - aeval g' p ∈ Io S τ ^ (n + 1) := by
  have hcg : ∀ i, constantCoeff (g i) = 0 := fun i => ccmem_lemma_2 (n := 0) (hg i)
  induction n with
  | zero =>
    intro p _
    refine ⟨by simp, weak_lemma_24 (by norm_num) (base_lemma_17 g g' hgg p)⟩
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      obtain ⟨h1, h2⟩ := ih a ha
      have hb0 : coeff 0 b = 0 := ccmem_lemma_2 (n := 0) (p := b) (by rwa [zero_add, pow_one])
      have hb1 : aeval g b ∈ Io S τ ^ 1 := by
        apply memcc_lemma_19
        rw [ccaeval_lemma_3 g hcg]
        exact hb0
      have hb2 : aeval g b - aeval g' b ∈ Io S τ ^ 2 := base_lemma_17 g g' hgg b
      have hb3 : aeval g' b ∈ Io S τ ^ 1 := by
        have h := Ideal.sub_mem _ hb1 (weak_lemma_24 (by norm_num) hb2)
        simpa using h
      constructor
      · rw [map_mul, pow_succ]
        exact Ideal.mul_mem_mul h1 (by rwa [pow_one] at hb1)
      · rw [map_mul, map_mul]
        have e : aeval g a * aeval g b - aeval g' a * aeval g' b =
            aeval g a * (aeval g b - aeval g' b) + (aeval g a - aeval g' a) * aeval g' b := by ring
        rw [e]
        have k1 := Ideal.mul_mem_mul h1 hb2
        have k2 := Ideal.mul_mem_mul h2 hb3
        rw [← pow_add] at k1 k2
        have e1 : n + 2 = n + 1 + 1 := by omega
        rw [e1] at k1
        exact Ideal.add_mem _ k1 k2
    · intro x y hx hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      constructor
      · rw [map_add]
        exact Ideal.add_mem _ hx1 hy1
      · rw [map_add, map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx2 hy2
private theorem ev2sub_lemma_25 {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S)
    (hu : ∀ i, u i ∈ Io S τ ^ 1) (hv : ∀ i, v i ∈ Io S τ ^ 1)
    (huu : ∀ i, u i - u' i ∈ Io S τ ^ 2) (hvv : ∀ i, v i - v' i ∈ Io S τ ^ 2)
    (n : ℕ) (p : MvPolynomial (Fin 2 × Fin d) S) (hp : p ∈ Io S (Fin 2 × Fin d) ^ n) :
    ev2 p u v ∈ Io S τ ^ n ∧ ev2 p u v - ev2 p u' v' ∈ Io S τ ^ (n + 1) := by
  refine subst_lemma_18 _ _ ?_ ?_ n p hp
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using hu i
    · simpa using hv i
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using huu i
    · simpa using hvv i
private theorem wtdeg_lemma_20 {σ : Type} (e : σ →₀ ℕ) : Finsupp.weight 1 e = Finsupp.degree e := by
  rw [Finsupp.weight_apply]
  show (e.sum fun i c => c • (1 : σ → ℕ) i) = ∑ i ∈ e.support, e i
  simp [Finsupp.sum]
private theorem hX_lemma_22 {σ : Type} (i : σ) : (X i : MvPolynomial σ S).IsHomogeneous 1 := by
  classical
  intro e he
  rw [coeff_X'] at he
  split_ifs at he with h
  · rw [← h]
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  · exact absurd rfl he
private theorem homog_lemma_21 {σ τ : Type} {p : MvPolynomial σ S} {j : ℕ} (hp : p.IsHomogeneous j)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous 1) : (aeval g p).IsHomogeneous j := by
  have h := hp.eval₂ C g (fun r => isHomogeneous_C _ r) hg
  rw [one_mul] at h
  rw [aeval_def, algebraMap_eq]
  exact h
private theorem ev2homog_lemma_23 {τ : Type} {p : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ}
    (hp : p.IsHomogeneous j) (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1)
    (hv : ∀ i, (v i).IsHomogeneous 1) : (ev2 p u v).IsHomogeneous j := by
  apply homog_lemma_21 hp
  rintro ⟨k, i⟩
  fin_cases k
  · simpa using hu i
  · simpa using hv i
private theorem zeroOf_lemma_26 {τ : Type} {p : MvPolynomial τ S} {j : ℕ} (hh : p.IsHomogeneous j)
    (hp : p ∈ Io S τ ^ (j + 1)) : p = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h1 : Finsupp.weight 1 e = j := hh he
  have h2 := (memIo_lemma (j + 1) p).1 hp e (MvPolynomial.mem_support_iff.2 he)
  rw [wtdeg_lemma_20] at h1
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) :
    ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
          ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) ∧
      ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) = homogeneousComponent j (P - 1) := by
  have hxJ : ∀ (k : Fin 3) (i : Fin d), xs S d k i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have hyJ : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have haJ : ∀ i, xs S d (0 : Fin 3) i + xs S d 1 i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun i => Ideal.add_mem _ (hxJ 0 i) (hxJ 1 i)
  have hfJ : ∀ i, fF i ∈ Io S (Fin 3 × Fin d) ^ 1 := by
    intro i
    have h := Ideal.add_mem _ (weak_lemma_24 (by norm_num) (hF i)) (haJ i)
    simpa using h
  have hR : P - 1 - homogeneousComponent j (P - 1) ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
    have hP' := hP
    rw [memIo_lemma] at hP' ⊢
    intro x hx
    rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hx
    split_ifs at hx with hxj
    · simp at hx
    · have hxQ : x ∈ (P - 1).support := by
        rw [MvPolynomial.mem_support_iff]
        simpa using hx
      have := hP' x hxQ
      omega
  have hQj := homogeneousComponent_isHomogeneous j (P - 1)
  have hXh : ∀ (k : Fin 3) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have hYh : ∀ (k : Fin 2) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have z2 : ∀ (w : Fin d → MvPolynomial (Fin 3 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 3 × Fin d) ^ 2 := by
    intro w i
    simp
  have y2 : ∀ (w : Fin d → MvPolynomial (Fin 2 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro w i
    simp
  constructor
  · have m1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hph1
    have m2 := (ev2sub_lemma_25 fF (xs S d (2 : Fin 3)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i)
      (xs S d (2 : Fin 3)) hfJ (hxJ 2) hF (z2 _) j (P - 1) hP).2
    have m3 := (ev2sub_lemma_25 (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3))
      (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) haJ (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have t4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have t5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have m6 : ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := by
      have h := Ideal.mul_mem_mul t4 t5
      rw [← pow_add] at h
      exact weak_lemma_24 (by omega) h
    have hE : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) = 0 := by
      apply zeroOf_lemma_26
      · exact ((ev2homog_lemma_23 hQj _ _ (fun i => (hXh 0 i).add (hXh 1 i)) (hXh 2)).sub
          (ev2homog_lemma_23 hQj _ _ (hXh 0) (hXh 2))).sub (ev2homog_lemma_23 hQj _ _ (hXh 1) (hXh 2))
      · have hid : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) =
            (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) -
            (ev2 (P - 1) fF (xs S d 2) - ev2 (P - 1) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) +
            ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
          (Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3) m4) m5) m6
    linear_combination hE
  · have s1 : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hsym
    have s2 := (ev2sub_lemma_25 (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2)) (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2))
      (hyJ 1) (hyJ 0) (y2 _) (y2 _) (j + 1) _ hR).1
    have hE : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) = 0 := by
      apply zeroOf_lemma_26
      · exact (ev2homog_lemma_23 hQj _ _ (hYh 1) (hYh 0)).sub hQj
      · have hid : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) =
            (ev2 P (xs S d 1) (xs S d 0) - P) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) +
            (P - 1 - homogeneousComponent j (P - 1)) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.sub_mem _ s1 s2) hR
    linear_combination hE
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
