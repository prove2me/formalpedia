-- Prove2me | solution 1 for BinarySketchTruncation.Opposite.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:01:49.224344+00:00
-- url     : https://prove2.me/submissions/12c633e6-7527-4bd9-8a08-f7792627ecb7

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Model
import Theorems.Thm_BinarySketchTruncation_Opposite_proposition_1
import Theorems.Thm_BinarySketchTruncation_Opposite_proposition_2

section
namespace BinarySketchTruncation.Dev.Thm1
open BinarySketchTruncation.Opposite

/-! ### General dominance lemmas -/

lemma map_toReal {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (μ : PMF S) (f : S → T) (t : T) :
    ((μ.map f) t).toReal = ∑ s, (μ s).toReal * (if f s = t then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : f s = t
    · simp [h]
    · simp [h, Ne.symm h]
  · intro s _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · simp

lemma dom_trans {S T U : Type} [Fintype S] [Fintype T] [Fintype U]
    {P : Experiment S} {Q : Experiment T} {R : Experiment U}
    (h1 : Dominates P Q) (h2 : Dominates Q R) : Dominates P R := by
  obtain ⟨K1, ⟨hK1a, hK1b⟩, hK1c⟩ := h1
  obtain ⟨K2, ⟨hK2a, hK2b⟩, hK2c⟩ := h2
  refine ⟨fun s u => ∑ t, K1 s t * K2 t u, ⟨?_, ?_⟩, ?_⟩
  · intro s u
    exact Finset.sum_nonneg fun t _ => mul_nonneg (hK1a _ _) (hK2a _ _)
  · intro s
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK2b, mul_one]
    exact hK1b s
  · intro h u
    rw [hK2c]
    simp_rw [hK1c, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp_rw [mul_assoc, ← Finset.mul_sum]

lemma dom_map {S T : Type} [Fintype S] [Fintype T] [DecidableEq T]
    (P : Experiment S) (g : S → T) : Dominates P (fun h => (P h).map g) := by
  refine ⟨fun s t => if g s = t then 1 else 0, ⟨?_, ?_⟩, ?_⟩
  · intro s t; dsimp only; split_ifs <;> norm_num
  · intro s; simp
  · intro h t; exact map_toReal _ _ _

lemma dom_of_eq {S T : Type} [Fintype S] [Fintype T]
    {P : Experiment S} {Q Q' : Experiment T} (h : Dominates P Q) (e : Q = Q') :
    Dominates P Q' := e ▸ h

/-! ### Laws -/

lemma add_add_self' {n : ℕ} (x z : Vec n) : x + (x + z) = z := by
  funext i
  have h : x i + x i = 0 := CharTwo.add_self_eq_zero (x i)
  simp [← add_assoc, h]

lemma joint_map_sum {n : ℕ} {T : Type} (p : Bias) (f : Vec n → T) :
    (jointLaw n p).map (fun xy => f (xy.1 + xy.2)) = (cubeLaw n p).map f := by
  unfold jointLaw
  rw [PMF.map_bind]
  have : ∀ x : Vec n, ((cubeLaw n p).map (fun z => (x, x + z))).map
      (fun xy => f (xy.1 + xy.2)) = (cubeLaw n p).map f := by
    intro x
    rw [PMF.map_comp]
    congr 1
    funext z
    simp [Function.comp, add_add_self']
  simp_rw [this]
  exact PMF.bind_const _ _

/-! ### Linear algebra: rank factorization through an information set of columns -/

lemma la {m n : ℕ} (M : Matrix (Fin m) (Fin n) Bit) :
    ∃ (e : Fin M.rank → Fin n) (a : Fin n → Fin M.rank → Bit)
      (C : Matrix (Fin m) (Fin M.rank) Bit),
      Function.Injective e ∧ (∀ i i', a (e i') i = if i = i' then 1 else 0) ∧
      ∀ z : Vec n, M.mulVec z = C.mulVec (fun i => ∑ j, a j i * z j) := by
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' Bit M.col
  have : Fintype κ := Fintype.ofInjective f hf
  have hcard : Fintype.card κ = M.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli]
  let σ : Fin M.rank ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  have h2 : ∀ j, M.col j ∈ Submodule.span Bit (Set.range (M.col ∘ f)) := by
    intro j
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  have h3 : ∀ j, ∃ c : Fin M.rank → Bit, ∑ i, c i • M.col (f (σ i)) = M.col j := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Bit).1 (h2 j)
    refine ⟨fun i => c (σ i), ?_⟩
    rw [← hc]
    exact Equiv.sum_comp σ (fun k => c k • (M.col ∘ f) k)
  choose c hc using h3
  let e : Fin M.rank → Fin n := fun i => f (σ i)
  have he : Function.Injective e := fun x y hxy => σ.injective (hf hxy)
  let a : Fin n → Fin M.rank → Bit := fun j i =>
    if ∃ i', e i' = j then (if e i = j then 1 else 0) else c j i
  have ha : ∀ j, ∑ i, a j i • M.col (e i) = M.col j := by
    intro j
    by_cases hj : ∃ i', e i' = j
    · obtain ⟨i0, rfl⟩ := hj
      have hex : ∃ i', e i' = e i0 := ⟨i0, rfl⟩
      simp only [a, if_pos hex, he.eq_iff]
      simp
    · simp only [a, if_neg hj]
      exact hc j
  refine ⟨e, a, fun r i => M r (e i), he, ?_, ?_⟩
  · intro i i'
    have hex : ∃ i'', e i'' = e i' := ⟨i', rfl⟩
    simp only [a, if_pos hex, he.eq_iff]
  · intro z
    funext r
    have hM : ∀ j, M r j = ∑ i, a j i * M r (e i) := by
      intro j
      have := congrFun (ha j) r
      simpa [Matrix.col, Finset.sum_apply] using this.symm
    simp only [Matrix.mulVec, dotProduct]
    calc ∑ j, M r j * z j = ∑ j, (∑ i, a j i * M r (e i)) * z j :=
          Finset.sum_congr rfl fun j _ => by rw [← hM j]
      _ = _ := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-! ### Product decomposition of the cube law -/

noncomputable def cubeG (ι : Type) [Fintype ι] [DecidableEq ι] (p : Bias) : PMF (ι → Bit) :=
  PMF.ofFintype (fun x => ∏ i, bitLaw p (x i)) (by
    rw [← Fintype.prod_sum]
    have hs : ∑ b : Bit, bitLaw p b = 1 := by
      simpa only [tsum_fintype] using (bitLaw p).tsum_coe
    simp only [hs, Finset.prod_const_one])

noncomputable def prodPMF {α β : Type} (P : PMF α) (Q : PMF β) : PMF (α × β) :=
  P.bind (fun u => Q.map (Prod.mk u))

lemma prodPMF_apply {α β : Type} (P : PMF α) (Q : PMF β) (u : α) (w : β) :
    prodPMF P Q (u, w) = P u * Q w := by
  classical
  unfold prodPMF
  rw [PMF.bind_apply, tsum_eq_single u]
  · congr 1
    rw [PMF.map_apply, tsum_eq_single w]
    · simp
    · intro w' hw'
      simp [Ne.symm hw']
  · intro u' hu'
    rw [PMF.map_apply]
    simp [Ne.symm hu']

lemma prodPMF_map_fst {α β : Type} (P : PMF α) (Q : PMF β) :
    (prodPMF P Q).map Prod.fst = P := by
  unfold prodPMF
  rw [PMF.map_bind]
  have : ∀ u : α, (Q.map (Prod.mk u)).map Prod.fst = PMF.pure u := by
    intro u
    rw [PMF.map_comp]
    exact PMF.map_const Q u
  simp_rw [this]
  exact PMF.bind_pure P

lemma map_equiv_apply {α β : Type} (μ : PMF α) (Θ : α ≃ β) (q : β) :
    (μ.map Θ) q = μ (Θ.symm q) := by
  rw [PMF.map_apply, tsum_eq_single (Θ.symm q)]
  · simp
  · intro b hb
    have : q ≠ Θ b := fun h => hb (by rw [h]; simp)
    simp [this]

lemma cubeLaw_apply {n : ℕ} (p : Bias) (z : Vec n) :
    cubeLaw n p z = ∏ i, bitLaw p (z i) := by
  unfold cubeLaw; rw [PMF.ofFintype_apply]

lemma cubeG_apply {ι : Type} [Fintype ι] [DecidableEq ι] (p : Bias) (z : ι → Bit) :
    cubeG ι p z = ∏ i, bitLaw p (z i) := by
  unfold cubeG; rw [PMF.ofFintype_apply]

section decomp
variable {n k : ℕ} (e : Fin k → Fin n)

/-- Split a vector into its coordinates along `e` and the remaining coordinates. -/
noncomputable def Theta (he : Function.Injective e) : Vec n ≃ Vec k × ({j // j ∉ Finset.univ.image e} → Bit) where
  toFun z := (fun i => z (e i), fun j => z j.1)
  invFun q := fun j =>
    if h : j ∈ Finset.univ.image e then q.1 (Classical.choose (Finset.mem_image.1 h))
    else q.2 ⟨j, h⟩
  left_inv z := by
    funext j
    by_cases h : j ∈ Finset.univ.image e
    · simp only [dif_pos h]
      exact congrArg z (Classical.choose_spec (Finset.mem_image.1 h)).2
    · simp [h]
  right_inv q := by
    ext1
    · funext i
      have h : e i ∈ Finset.univ.image e := Finset.mem_image_of_mem e (Finset.mem_univ i)
      simp only [dif_pos h]
      exact congrArg q.1 (he (Classical.choose_spec (Finset.mem_image.1 h)).2)
    · funext j
      simp [j.2]

lemma cube_decomp (he : Function.Injective e) (p : Bias) :
    (cubeLaw n p).map (Theta e he) =
      prodPMF (cubeLaw k p) (cubeG {j // j ∉ Finset.univ.image e} p) := by
  ext q
  obtain ⟨z, rfl⟩ := (Theta e he).surjective q
  rw [map_equiv_apply, Equiv.symm_apply_apply]
  rw [show Theta e he z = ((fun i => z (e i)), fun j => z j.1) from rfl, prodPMF_apply,
    cubeLaw_apply, cubeG_apply, cubeLaw_apply, ← Fintype.prod_subtype_mul_prod_subtype
      (fun j => j ∈ Finset.univ.image e) (fun j => bitLaw p (z j))]
  congr 1
  convert (Finset.prod_coe_sort (Finset.univ.image e) (fun j => bitLaw p (z j))).trans
    (Finset.prod_image (fun a _ b _ h => he h))

lemma cube_marginal (he : Function.Injective e) (p : Bias) :
    (cubeLaw n p).map (fun z i => z (e i)) = cubeLaw k p := by
  have h1 : (fun z : Vec n => fun i => z (e i)) = Prod.fst ∘ Theta e he := rfl
  rw [h1, ← PMF.map_comp, cube_decomp e he, prodPMF_map_fst]

lemma W_split (he : Function.Injective e) (a : Fin n → Fin k → Bit)
    (ha : ∀ i i', a (e i') i = if i = i' then 1 else 0) (z : Vec n) (i : Fin k) :
    ∑ j, a j i * z j = z (e i) +
      ∑ j : {j // j ∉ Finset.univ.image e}, a j.1 i * z j.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ Finset.univ.image e)
    (fun j => a j i * z j)]
  congr 1
  convert (Finset.sum_coe_sort (Finset.univ.image e) (fun j => a j i * z j)).trans
    ((Finset.sum_image (fun x _ y _ h => he h)).trans ?_)
  simp [ha]

lemma law_W (he : Function.Injective e) (a : Fin n → Fin k → Bit)
    (ha : ∀ i i', a (e i') i = if i = i' then 1 else 0) (p : Bias) :
    (cubeLaw n p).map (fun z i => ∑ j, a j i * z j) =
      (cubeLaw k p).bind (fun u =>
        ((cubeG {j // j ∉ Finset.univ.image e} p).map
          (fun w i => ∑ j : {j // j ∉ Finset.univ.image e}, a j.1 i * w j)).map
          (fun v => u + v)) := by
  have h1 : (fun z : Vec n => fun i => ∑ j, a j i * z j) =
      (fun q : Vec k × ({j // j ∉ Finset.univ.image e} → Bit) =>
        q.1 + fun i => ∑ j : {j // j ∉ Finset.univ.image e}, a j.1 i * q.2 j) ∘ Theta e he := by
    funext z i
    simp only [Function.comp, Pi.add_apply]
    exact W_split e he a ha z i
  rw [h1, ← PMF.map_comp, cube_decomp e he]
  unfold prodPMF
  rw [PMF.map_bind]
  refine congrArg _ (funext fun u => ?_)
  rw [PMF.map_comp, PMF.map_comp]
  rfl

end decomp

/-! ### Assembly -/

lemma prefix_dom_cube {n k : ℕ} (hk : k ≤ n) (p₀ p₁ : Bias) :
    Dominates (prefixExperiment n k p₀ p₁) (cubeExperiment k p₀ p₁) := by
  refine dom_of_eq (dom_map (prefixExperiment n k p₀ p₁) (fun q => q.1 + q.2)) ?_
  funext h
  unfold prefixExperiment cubeExperiment
  rw [PMF.map_comp]
  have h1 : ((fun q : Vec k × Vec k => q.1 + q.2) ∘ fun xy : Vec n × Vec n =>
      (takePrefix k xy.1, takePrefix k xy.2)) =
      fun xy => (fun z : Vec n => fun i : Fin k => z (Fin.castLE hk i)) (xy.1 + xy.2) := by
    funext xy i
    simp [takePrefix, Function.comp, i.2.trans_le hk]
    rfl
  rw [h1, joint_map_sum _ (fun z : Vec n => fun i : Fin k => z (Fin.castLE hk i)), cube_marginal (Fin.castLE hk) (Fin.castLE_injective hk)]

lemma sum_dom {m n : ℕ} (p₀ p₁ : Bias) (hop : OppositeSides p₀ p₁)
    (M : Matrix (Fin m) (Fin n) Bit) :
    Dominates (prefixExperiment n M.rank p₀ p₁) (sumSketchExperiment p₀ p₁ M) := by
  obtain ⟨e, a, C, he, ha, hM⟩ := la M
  have hk : M.rank ≤ n := Matrix.rank_le_width M
  let V : ({j // j ∉ Finset.univ.image e} → Bit) → Vec M.rank := fun w i =>
    ∑ j : {j // j ∉ Finset.univ.image e}, a j.1 i * w j
  let ν : Experiment (Vec M.rank) := fun h =>
    (cubeG {j // j ∉ Finset.univ.image e} (biasAt p₀ p₁ h)).map V
  have h2 : Dominates (cubeExperiment M.rank p₀ p₁)
      (independentSum (cubeExperiment M.rank p₀ p₁) ν) :=
    ⟨_, ((proposition_2 M.rank p₀ p₁).2 (Or.inr hop) ν)⟩
  have h3 := dom_map (independentSum (cubeExperiment M.rank p₀ p₁) ν) C.mulVec
  refine dom_trans (prefix_dom_cube hk p₀ p₁) (dom_trans h2 (dom_of_eq h3 ?_))
  funext h
  unfold sumSketchExperiment independentSum cubeExperiment
  rw [joint_map_sum (biasAt p₀ p₁ h) M.mulVec]
  have h4 : M.mulVec = C.mulVec ∘ (fun z : Vec n => fun i => ∑ j, a j i * z j) := by
    funext z; exact hM z
  rw [h4, ← PMF.map_comp, law_W e he a ha, PMF.map_bind]

end BinarySketchTruncation.Dev.Thm1

namespace BinarySketchTruncation.Opposite
open BinarySketchTruncation.Dev.Thm1

theorem chk_theorem_1 {n mA mB : ℕ} (p₀ p₁ : Bias)
    (hop : OppositeSides p₀ p₁)
    (A : Matrix (Fin mA) (Fin n) Bit) (B : Matrix (Fin mB) (Fin n) Bit) :
    Dominates (prefixExperiment n (min A.rank B.rank) p₀ p₁)
      (sketchExperiment p₀ p₁ A B) := by
  obtain ⟨-, -, hA, hB⟩ := proposition_1 p₀ p₁ A B
  rcases le_total A.rank B.rank with h | h
  · rw [min_eq_left h]
    exact dom_trans (sum_dom p₀ p₁ hop A) hA
  · rw [min_eq_right h]
    exact dom_trans (sum_dom p₀ p₁ hop B) hB

end BinarySketchTruncation.Opposite
end

theorem solution : type_of% @BinarySketchTruncation.Opposite.chk_theorem_1 := @BinarySketchTruncation.Opposite.chk_theorem_1
