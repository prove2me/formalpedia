-- Prove2me | solution 1 for F3SubsetSum.corollary_4_18
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T04:16:51.74173+00:00
-- url     : https://prove2.me/submissions/4a955e4e-2b1a-4ebd-99ca-598907760513

import Definitions.Def_F3SubsetSum_BorelAction
import Definitions.Def_F3SubsetSum_MonomialShadow
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Localization.FractionRing
import Definitions.Def_F3SubsetSum_SampleImage
import Definitions.Def_F3SubsetSum_SymbolicRank
import Definitions.Def_F3SubsetSum_RootMultiplicity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open F3SubsetSum MvPolynomial
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false

namespace RankProof
section
variable {K : Type*} [Field K]
private noncomputable def dualCoords (J : Type*) [Fintype J] [DecidableEq J] :
    Module.Dual K (J → K) →ₗ[K] (J → K) where
  toFun ℓ j := ℓ (Pi.single j 1)
  map_add' := by intro ℓ η; rfl
  map_smul' := by intro c ℓ; rfl

private lemma dualCoords_injective (J : Type*) [Fintype J] [DecidableEq J] :
    Function.Injective (dualCoords (K := K) J) := by
  classical
  intro ℓ η h
  apply (Pi.basisFun K J).ext
  intro j
  have hh := congrFun h j
  change ℓ (Pi.single j 1) = η (Pi.single j 1) at hh
  simpa only [Pi.basisFun_apply] using hh

private lemma eval_generic (q n D : ℕ) (a : Fin n → K)
    (ℓ : Module.Dual K (Rd K n q D)) (β : ReducedMono n q (D-2)) :
    eval a (genericEntry K n q D ℓ β) = contraction K n q D a ℓ (Pi.single β 1) := by
  classical
  let w := Rd.toPoly K n q (D-2) (Pi.single β 1)
  let G : MvPolynomial (Fin n) K →ₗ[K] K :=
    ℓ.comp ((Rd.ofPoly K n q D).comp (LinearMap.mulRight K w))
  have hlin : linForm a ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (a i * a j) • (X i * X j) := by
    unfold linForm
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Algebra.smul_def, algebraMap_eq]
    rw [map_mul]
    ring
  have hG : contraction K n q D a ℓ (Pi.single β 1) = G (linForm a ^ 2) := rfl
  rw [hG, hlin]
  simp only [map_sum, map_smul, smul_eq_mul]
  unfold genericEntry
  simp only [map_sum, map_mul, eval_C, eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _ = (a i * a j) * ℓ (mulMap K n q (X i * X j) (D-2) D (Pi.single β 1))
  ring

end
end RankProof

namespace BorelProof
set_option maxHeartbeats 400000
set_option linter.all false
section

private lemma completion {S F L ι τ : Type*} [CommRing S] [Field F] [Field L]
    [Fintype ι] [Fintype τ] [DecidableEq τ] (M : Matrix ι τ S) (l : S →+* F) :
    ∃ B : Matrix τ τ S, l B.det ≠ 0 ∧ ∀ f : S →+* L,
      (B.map f).rank ≤ (M.map f).rank + (Fintype.card τ - (M.map l).rank) := by
  classical
  let P := S
  let ρ := (M.map l).rank
  obtain ⟨s, hs, hsp, hsi⟩ := exists_linearIndependent F (Set.range (M.map l).row)
  let E : Set (τ → F) := Set.range (Pi.basisFun F τ)
  obtain ⟨b, hb, hsub, hspan, hbi⟩ := exists_linearIndepOn_id_extension
    (show LinearIndepOn F id s from hsi) (Set.subset_union_left : s ⊆ s ∪ E)
  have hbtop : Submodule.span F b = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun F τ).span_eq]
    exact Submodule.span_le.mpr (fun v hv => hspan (Or.inr hv))
  letI : Finite s := hsi.finite
  letI : Finite b := hbi.finite
  letI : Fintype s := Fintype.ofFinite s
  letI : Fintype b := Fintype.ofFinite b
  have hcs : Fintype.card s = ρ := by
    have hh := finrank_span_eq_card hsi
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hsp] at hh
    change Fintype.card s = (M.map l).rank
    rw [Matrix.rank_eq_finrank_span_row]
    exact hh.symm
  have hcb : Fintype.card b = Fintype.card τ := by
    have hh := finrank_span_eq_card hbi
    change Module.finrank F (Submodule.span F (Set.range (fun v : b => v.val))) = Fintype.card b at hh
    rw [show Set.range (fun v : b => v.val) = b by ext v; simp, hbtop] at hh
    simpa using hh.symm
  let e : b ≃ τ := Fintype.equivOfCardEq hcb
  have hchoose (v : b) : ∃ r : τ → P, (∀ j, l (r j) = v.val j) ∧
      ((v.val ∈ s ∧ ∃ i, r = M i) ∨ (v.val ∉ s ∧ ∃ j, r = Pi.single j 1)) := by
    by_cases hv : v.val ∈ s
    · obtain ⟨i, hi⟩ := hs hv
      exact ⟨M i, fun j => congrFun hi j, Or.inl ⟨hv, i, rfl⟩⟩
    · have hvE : v.val ∈ E := (hb v.property).resolve_left hv
      obtain ⟨j, hj⟩ := hvE
      refine ⟨Pi.single j 1, ?_, Or.inr ⟨hv, j, rfl⟩⟩
      intro k
      rw [← hj]
      simp [Pi.single_apply]
  choose R hR htype using hchoose
  let B : Matrix τ τ P := fun i j => R (e.symm i) j
  have hlift : B.map l = fun i : τ => ((e.symm i).val : τ → F) := by
    ext i j
    exact hR _ _
  have hind : LinearIndependent F (B.map l).row := by
    rw [hlift]
    exact hbi.comp e.symm e.symm.injective
  have hdetF : (B.map l).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hind)).ne_zero
  have hdet : l B.det ≠ 0 := by
    rw [l.map_det]
    exact hdetF
  let good : Finset τ := Finset.univ.filter (fun i => (e.symm i).val ∈ s)
  have hcg : good.card = ρ := by
    let f : {i : τ // i ∈ good} ≃ s :=
      { toFun := fun i => ⟨(e.symm i.val).val, (Finset.mem_filter.mp i.property).2⟩
        invFun := fun v => ⟨e ⟨v.val, hsub v.property⟩, by simp [good, v.property]⟩
        left_inv := by intro i; apply Subtype.ext; simp
        right_inv := by intro v; apply Subtype.ext; simp }
    rw [← hcs, ← Fintype.card_coe good]
    exact Fintype.card_congr f
  refine ⟨B, hdet, ?_⟩
  intro f
  let bad : Finset τ := Finset.univ \ good
  let extra : Finset (τ → L) := bad.image (B.map f).row
  let O : Submodule L (τ → L) := Submodule.span L (Set.range (M.map f).row)
  let E' : Submodule L (τ → L) := Submodule.span L (extra : Set (τ → L))
  have hE : Module.finrank L E' ≤ bad.card :=
    (finrank_span_finset_le_card extra).trans (Finset.card_image_le)
  have hspanB : Submodule.span L (Set.range (B.map f).row) ≤ O ⊔ E' := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    by_cases hi : i ∈ good
    · have his : (e.symm i).val ∈ s := (Finset.mem_filter.mp hi).2
      rcases htype (e.symm i) with ⟨_, k, hk⟩ | ⟨hn, _⟩
      · apply (show O ≤ O ⊔ E' from le_sup_left)
        apply Submodule.subset_span
        refine ⟨k, ?_⟩
        ext j
        change f (M k j) = f (R (e.symm i) j)
        rw [hk]
      · exact False.elim (hn his)
    · apply (show E' ≤ O ⊔ E' from le_sup_right)
      apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨i, by simp [bad, hi], rfl⟩
  have hdim := (Submodule.finrank_mono hspanB).trans
    ((Submodule.finrank_add_le_finrank_add_finrank O E').trans (Nat.add_le_add_left hE _))
  have hbad : bad.card = Fintype.card τ - ρ := by
    dsimp only [bad]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcg]
  rw [Matrix.rank_eq_finrank_span_row]
  change Module.finrank L (Submodule.span L (Set.range (B.map f).row)) ≤ _
  rw [Matrix.rank_eq_finrank_span_row, ← hbad]
  exact hdim


private def Leads {K I : Type*} [Field K] (w : I → ℕ) (W : Submodule K (I → K)) (i : I) : Prop :=
  ∃ v ∈ W, v i ≠ 0 ∧ ∀ j, w i < w j → v j = 0

private noncomputable def initialFamily {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (W : Submodule K (I → K)) : Finset I := by
  classical
  exact Finset.univ.filter (Leads w W)

private lemma mem_initialFamily {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (W : Submodule K (I → K)) (i : I) : i ∈ initialFamily w W ↔ Leads w W i := by
  classical
  simp [initialFamily]

private noncomputable def initialRows {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (W : Submodule K (I → K)) (i : initialFamily w W) : I → K := by
  classical
  let v := Classical.choose ((mem_initialFamily w W i.val).mp i.property)
  exact (v i.val)⁻¹ • v

private lemma initialRows_properties {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (W : Submodule K (I → K)) (i : initialFamily w W) :
    initialRows w W i ∈ W ∧ initialRows w W i i.val = 1 ∧
      ∀ j, w i.val < w j → initialRows w W i j = 0 := by
  classical
  let hv := Classical.choose_spec ((mem_initialFamily w W i.val).mp i.property)
  refine ⟨W.smul_mem _ hv.1, ?_, ?_⟩
  · exact inv_mul_cancel₀ hv.2.1
  · intro j hj
    simp only [initialRows, Pi.smul_apply, smul_eq_mul]
    rw [hv.2.2 j hj, mul_zero]

private lemma initialRows_independent {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (W : Submodule K (I → K)) :
    LinearIndependent K (initialRows w W) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hi
  let S : Finset (initialFamily w W) := Finset.univ.filter (fun j => c j ≠ 0)
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image (fun j => w j.val)
    ⟨i, by simp [S, hi]⟩
  have hkn : c k ≠ 0 := (Finset.mem_filter.mp hk).2
  have he := congrFun hc k.val
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  have hs : (∑ j : initialFamily w W, c j * initialRows w W j k.val) = c k := by
    rw [Finset.sum_eq_single k]
    · rw [(initialRows_properties w W k).2.1, mul_one]
    · intro j _ hj
      by_cases hz : c j = 0
      · rw [hz, zero_mul]
      · have hle := hmax j (by simp [S, hz])
        have hne : w j.val ≠ w k.val := fun h => hj (Subtype.ext (hw h))
        rw [(initialRows_properties w W j).2.2 k.val (lt_of_le_of_ne hle hne), mul_zero]
    · simp
  exact hkn (hs.symm.trans he)

private lemma initialRows_span {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (W : Submodule K (I → K)) :
    Submodule.span K (Set.range (initialRows w W)) = W := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact (initialRows_properties w W i).1
  · have hind (d : ℕ) : ∀ v ∈ W, (∀ j, d ≤ w j → v j = 0) →
        v ∈ Submodule.span K (Set.range (initialRows w W)) := by
      induction d with
      | zero =>
        intro v hv hzero
        have hz : v = 0 := by ext j; exact hzero j (Nat.zero_le _)
        rw [hz]; exact Submodule.zero_mem _
      | succ d ih =>
        intro v hv hbound
        by_cases hex : ∃ i, w i = d ∧ v i ≠ 0
        · obtain ⟨i, hi, hvi⟩ := hex
          have hlead : Leads w W i := ⟨v, hv, hvi, fun j hj => hbound j (by omega)⟩
          let a : initialFamily w W := ⟨i, (mem_initialFamily w W i).mpr hlead⟩
          let u := v - v i • initialRows w W a
          have hu : u ∈ W := W.sub_mem hv (W.smul_mem _ (initialRows_properties w W a).1)
          have hub (j : I) (hj : d ≤ w j) : u j = 0 := by
            by_cases hij : j = i
            · subst j
              simp [u, a, (initialRows_properties w W a).2.1]
            · have hjgt : d < w j := lt_of_le_of_ne hj (by intro he; exact hij (hw (he.symm.trans hi.symm)))
              have hr := (initialRows_properties w W a).2.2 j (by simpa [a, hi] using hjgt)
              simp [u, hbound j (by omega), hr]
          have huS := ih u hu hub
          have haS : initialRows w W a ∈ Submodule.span K (Set.range (initialRows w W)) :=
            Submodule.subset_span ⟨a, rfl⟩
          have hh := (Submodule.span K (Set.range (initialRows w W))).add_mem huS
            ((Submodule.span K (Set.range (initialRows w W))).smul_mem (v i) haS)
          simpa only [u, sub_add_cancel] using hh
        · apply ih v hv
          intro j hj
          by_cases heq : w j = d
          · by_contra hn
            exact hex ⟨j, heq, hn⟩
          · exact hbound j (by omega)
    intro v hv
    apply hind ((Finset.univ : Finset I).sup w + 1) v hv
    intro j hj
    have hle := Finset.le_sup (f := w) (Finset.mem_univ j)
    omega

private lemma initialFamily_card {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (W : Submodule K (I → K)) :
    (initialFamily w W).card = Module.finrank K W := by
  have h := finrank_span_eq_card (initialRows_independent w hw W)
  rw [initialRows_span w hw W] at h
  simpa only [Fintype.card_coe] using h.symm


private lemma rank_specialization {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq J]
    {n : ℕ} (M : Matrix I J (MvPolynomial (Fin n) K)) (a : Fin n → K) :
    (M.map (eval a)).rank ≤
      (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank := by
  classical
  let P := MvPolynomial (Fin n) K
  let F := FractionRing P
  let l : P →+* F := algebraMap P F
  obtain ⟨B, hB, hb⟩ := completion (L := F) M (eval a)
  have hn : B.det ≠ 0 := by intro h; rw [h, map_zero] at hB; exact hB rfl
  have hBF : (B.map l).det ≠ 0 := by
    change (l.mapMatrix B).det ≠ 0
    rw [← l.map_det]
    exact fun h => hn ((IsFractionRing.injective P F) (h.trans l.map_zero.symm))
  have hr := Matrix.rank_of_det_ne_zero hBF
  have hh := hb l
  rw [hr] at hh
  have hle := (M.map (eval a)).rank_le_card_width
  change (M.map (eval a)).rank ≤ (M.map l).rank
  omega

private lemma polynomial_rank_closed {K I J : Type*} [Field K] [Infinite K]
    [Fintype I] [Fintype J] [DecidableEq J] (M : Matrix I J (Polynomial K)) (r : ℕ)
    (hr : ∀ t : K, t ≠ 0 → (M.map (Polynomial.evalRingHom t)).rank ≤ r) :
    (M.map (Polynomial.evalRingHom 0)).rank ≤ r := by
  classical
  obtain ⟨B, hB, hb⟩ := completion (L := K) M (Polynomial.evalRingHom 0)
  have hn : B.det ≠ 0 := by intro h; rw [h, map_zero] at hB; exact hB rfl
  have hprod : B.det * Polynomial.X ≠ 0 := mul_ne_zero hn Polynomial.X_ne_zero
  obtain ⟨t, ht⟩ : ∃ t : K, Polynomial.eval t (B.det * Polynomial.X) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  have ht0 : t ≠ 0 := by intro h; subst t; simp at ht
  have hdet : (B.map (Polynomial.evalRingHom t)).det ≠ 0 := by
    change ((Polynomial.evalRingHom t).mapMatrix B).det ≠ 0
    rw [← (Polynomial.evalRingHom t).map_det]
    exact left_ne_zero_of_mul (by simpa using ht)
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have hh := hb (Polynomial.evalRingHom t)
  rw [hrank] at hh
  have hle := (M.map (Polynomial.evalRingHom 0)).rank_le_card_width
  have hrt := hr t ht0
  omega

private lemma generic_rank_attained {K I J : Type*} [Field K] [Infinite K]
    [Fintype I] [Fintype J] [DecidableEq J] {n : ℕ}
    (M : Matrix I J (MvPolynomial (Fin n) K)) :
    ∃ a : Fin n → K, (M.map (eval a)).rank =
      (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank := by
  classical
  let P := MvPolynomial (Fin n) K
  let F := FractionRing P
  let l : P →+* F := algebraMap P F
  obtain ⟨B, hB, hb⟩ := completion (L := K) M l
  have hn : B.det ≠ 0 := by intro h; rw [h, map_zero] at hB; exact hB rfl
  obtain ⟨a, ha⟩ : ∃ a : Fin n → K, eval a B.det ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (MvPolynomial.funext fun a => by simpa using h a)
  have hdet : (B.map (eval a)).det ≠ 0 := by
    change ((eval a).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    exact ha
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have hh := hb (eval a)
  rw [hrank] at hh
  have hle := (M.map l).rank_le_card_width
  have hspec := rank_specialization M a
  change (M.map (eval a)).rank ≤ (M.map l).rank at hspec
  exact ⟨a, by change (M.map (eval a)).rank = (M.map l).rank; omega⟩


private lemma mono_injective {n q d : ℕ} :
    Function.Injective (ReducedMono.toFinsupp : ReducedMono n q d → Fin n →₀ ℕ) := by
  intro a b h
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrFun (congrArg (fun f : Fin n →₀ ℕ => (f : Fin n → ℕ)) h) j

private lemma mono_degree {n q d : ℕ} (a : ReducedMono n q d) : a.toFinsupp.degree = d := by
  rw [Finsupp.degree_eq_sum]
  simpa [ReducedMono.toFinsupp, Finsupp.sum_fintype] using a.property

private lemma toPoly_coeff {K : Type*} [Field K] {n q d : ℕ} (v : Rd K n q d)
    (a : ReducedMono n q d) : coeff a.toFinsupp (Rd.toPoly K n q d v) = v a := by
  classical
  simp only [Rd.toPoly, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [show b.toFinsupp ≠ a.toFinsupp from fun h => hb (mono_injective h)]
  · simp

private lemma toPoly_single {K : Type*} [Field K] {n q d : ℕ} (a : ReducedMono n q d) :
    Rd.toPoly K n q d (Pi.single a 1) = monomial a.toFinsupp 1 := by
  classical
  simp only [Rd.toPoly, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

private lemma ofPoly_toPoly {K : Type*} [Field K] {n q d : ℕ} (v : Rd K n q d) :
    Rd.ofPoly K n q d (Rd.toPoly K n q d v) = v := by
  funext a
  exact toPoly_coeff v a

private lemma toPoly_homogeneous {K : Type*} [Field K] {n q d : ℕ} (v : Rd K n q d) :
    (Rd.toPoly K n q d v).IsHomogeneous d := by
  classical
  simp only [Rd.toPoly, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply IsHomogeneous.sum
  intro a _
  apply isHomogeneous_monomial
  exact mono_degree a

private noncomputable def truncIdeal (K : Type*) [Field K] (n q : ℕ) :
    Ideal (MvPolynomial (Fin n) K) := Ideal.span (Set.range fun i : Fin n => X i ^ q)

private lemma mem_truncIdeal {K : Type*} [Field K] {n q : ℕ} (p : MvPolynomial (Fin n) K) :
    p ∈ truncIdeal K n q ↔ ∀ a ∈ p.support, ∃ j, q ≤ a j := by
  classical
  have he : Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) K) ^ q) =
      (fun a : Fin n →₀ ℕ => monomial a (1 : K)) ''
        Set.range (fun i : Fin n => Finsupp.single i q) := by
    ext p
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Finsupp.single i q, ⟨i, rfl⟩, by rw [X_pow_eq_monomial]⟩
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [X_pow_eq_monomial]⟩
  unfold truncIdeal
  rw [he, mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff]

private lemma ofPoly_truncIdeal {K : Type*} [Field K] {n q d : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p ∈ truncIdeal K n q) :
    Rd.ofPoly K n q d p = 0 := by
  funext a
  change coeff a.toFinsupp p = 0
  by_contra h
  obtain ⟨j, hj⟩ := (mem_truncIdeal p).mp hp a.toFinsupp (mem_support_iff.mpr h)
  exact (Nat.not_le_of_gt (a.val j).isLt) hj

private lemma project_difference {K : Type*} [Field K] {n q d : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous d) :
    p - Rd.toPoly K n q d (Rd.ofPoly K n q d p) ∈ truncIdeal K n q := by
  classical
  apply (mem_truncIdeal _).mpr
  intro a ha
  by_contra h
  push Not at h
  let b : ReducedMono n q d := ⟨fun j => ⟨a j, h j⟩, by
    have hdeg : a.degree = d := by
      by_contra hh
      have hpc := hp.coeff_eq_zero hh
      have hqc := (toPoly_homogeneous (Rd.ofPoly K n q d p)).coeff_eq_zero hh
      have hn := mem_support_iff.mp ha
      exact hn (by simp [coeff_sub, hpc, hqc])
    simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hdeg⟩
  have hb : b.toFinsupp = a := by ext j; rfl
  have hn := mem_support_iff.mp ha
  apply hn
  rw [coeff_sub, ← hb, toPoly_coeff]
  exact sub_self _

private lemma linForm_homogeneous {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) :
    (linForm a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X K j).C_mul _

private lemma substitute_truncIdeal {K : Type*} [Field K] (q : ℕ) [Fact q.Prime]
    [CharP K q] {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (Fin n) K) (hp : p ∈ truncIdeal K n q) :
    aeval (fun j => linForm (cols G j)) p ∈ truncIdeal K n q := by
  let φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
    aeval (fun j => linForm (cols G j))
  have hle : truncIdeal K n q ≤ (truncIdeal K n q).comap φ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change φ (X j ^ q) ∈ truncIdeal K n q
    simp only [map_pow, aeval_X, φ]
    unfold linForm
    rw [sum_pow_char]
    apply Ideal.sum_mem
    intro i _
    rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  exact hle hp

private lemma project_mul {K : Type*} [Field K] {n q d e : ℕ}
    (p r : MvPolynomial (Fin n) K) (hr : r.IsHomogeneous d) :
    Rd.ofPoly K n q e (p * Rd.toPoly K n q d (Rd.ofPoly K n q d r)) =
      Rd.ofPoly K n q e (p * r) := by
  have h := ofPoly_truncIdeal (d := e) _
    ((truncIdeal K n q).mul_mem_left p (project_difference r hr))
  rw [mul_sub, map_sub, sub_eq_zero] at h
  exact h.symm

private lemma project_subst {K : Type*} [Field K] (q : ℕ) [Fact q.Prime]
    [CharP K q] {n d : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous d) :
    Rd.ofPoly K n q d (aeval (fun j => linForm (cols G j))
      (Rd.toPoly K n q d (Rd.ofPoly K n q d p))) =
      Rd.ofPoly K n q d (aeval (fun j => linForm (cols G j)) p) := by
  have h := ofPoly_truncIdeal (d := d) _
    (substitute_truncIdeal q G _ (project_difference p hp))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm


private noncomputable def subG {K : Type*} [Field K] {n : ℕ} (q : ℕ)
    (G : Matrix (Fin n) (Fin n) K) (d : ℕ) : Rd K n q d →ₗ[K] Rd K n q d :=
  substR q (fun j => linForm (cols G j)) d

private lemma subst_linForm {K : Type*} [Field K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (a : Fin n → K) :
    aeval (fun j => linForm (cols G j)) (linForm a) = linForm (G.mulVec a) := by
  simp only [linForm, map_sum, map_mul, aeval_C, aeval_X]
  simp only [linForm, Finset.mul_sum, ← mul_assoc, ← map_mul, cols,
    Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change C (a j) * C (G i j) * X i = C (G i j * a j) * X i
  rw [← map_mul, mul_comm (a j)]

private lemma linForm_unit {K : Type*} [Field K] {n : ℕ} (j : Fin n) :
    linForm (cols (1 : Matrix (Fin n) (Fin n) K) j) = X j := by
  classical
  simp [linForm, cols, Matrix.one_apply, eq_comm]

private lemma substitute_comp {K : Type*} [Field K] {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (p : MvPolynomial (Fin n) K) :
    aeval (fun j => linForm (cols G j)) (aeval (fun j => linForm (cols H j)) p) =
      aeval (fun j => linForm (cols (G * H) j)) p := by
  have he : (aeval (fun j => linForm (cols G j))).comp
      (aeval (fun j => linForm (cols H j))) =
      aeval (fun j => linForm (cols (G * H) j)) := by
    ext j
    simp only [AlgHom.comp_apply, aeval_X, subst_linForm]
    congr 1
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K => f p) he

private lemma subG_comp {K : Type*} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q]
    {n : ℕ} (G H : Matrix (Fin n) (Fin n) K) (d : ℕ) :
    (subG q G d).comp (subG q H d) = subG q (G * H) d := by
  apply LinearMap.ext
  intro v
  funext a
  change Rd.ofPoly K n q d (aeval (fun j => linForm (cols G j))
    (Rd.toPoly K n q d (Rd.ofPoly K n q d
      (aeval (fun j => linForm (cols H j)) (Rd.toPoly K n q d v))))) a = _
  rw [project_subst q G _ (by simpa using
    ((toPoly_homogeneous v).aeval (fun j => linForm (cols H j))
      (fun j => linForm_homogeneous _))), substitute_comp]
  rfl

private lemma subG_one {K : Type*} [Field K] {n q : ℕ} (d : ℕ) :
    subG q (1 : Matrix (Fin n) (Fin n) K) d = LinearMap.id := by
  have he : aeval (fun j => linForm (cols (1 : Matrix (Fin n) (Fin n) K) j)) =
      AlgHom.id K (MvPolynomial (Fin n) K) := by
    ext j
    simp only [aeval_X, linForm_unit, AlgHom.id_apply]
  apply LinearMap.ext
  intro v
  funext a
  change Rd.ofPoly K n q d (aeval (fun j => linForm (cols (1 : Matrix (Fin n) (Fin n) K) j))
    (Rd.toPoly K n q d v)) a = v a
  rw [he]
  exact congrFun (ofPoly_toPoly v) a

private noncomputable def subEquiv {K : Type*} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q]
    {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (hG : G.det ≠ 0) (d : ℕ) :
    Rd K n q d ≃ₗ[K] Rd K n q d :=
  LinearEquiv.ofLinear (subG q G d) (subG q G⁻¹ d)
    (by rw [subG_comp, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), subG_one])
    (by rw [subG_comp, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG), subG_one])

private lemma contraction_covariance {K : Type*} [Field K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hD : 2 ≤ D)
    (G : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ℓ : Module.Dual K (Rd K n q D)) :
    contraction K n q D a (ℓ.comp (subG q G D)) =
      (contraction K n q D (G.mulVec a) ℓ).comp (subG q G (D - 2)) := by
  apply LinearMap.ext
  intro v
  simp only [contraction, LinearMap.dualMap_apply', LinearMap.comp_apply,
    subG, substR, mulMap, LinearMap.mulLeft_apply]
  change ℓ (Rd.ofPoly K n q D (aeval (fun j => linForm (cols G j))
    (Rd.toPoly K n q D (Rd.ofPoly K n q D (linForm a ^ 2 * Rd.toPoly K n q (D - 2) v))))) =
    ℓ (Rd.ofPoly K n q D (linForm (G.mulVec a) ^ 2 *
      Rd.toPoly K n q (D - 2) (Rd.ofPoly K n q (D - 2)
        (aeval (fun j => linForm (cols G j)) (Rd.toPoly K n q (D - 2) v)))))
  have hp : (linForm a ^ 2 * Rd.toPoly K n q (D - 2) v).IsHomogeneous D := by
    convert ((linForm_homogeneous a).pow 2).mul (toPoly_homogeneous (n := n) (q := q) (d := D - 2) v) using 1 <;> omega
  rw [project_subst q G _ hp, map_mul, map_pow, subst_linForm]
  rw [project_mul _ _ (by simpa using ((toPoly_homogeneous (n := n) (q := q) (d := D - 2) v).aeval
    (fun j => linForm (cols G j)) (fun j => linForm_homogeneous _)))]

private noncomputable def dc {K : Type*} [Field K] {n q d : ℕ} :
    (ReducedMono n q d → K) ≃ₗ[K] Module.Dual K (Rd K n q d) :=
  (Pi.basisFun K (ReducedMono n q d)).constr K

private lemma dc_apply_single {K : Type*} [Field K] {n q d : ℕ}
    (v : ReducedMono n q d → K) (a : ReducedMono n q d) : dc (n := n) (q := q) (d := d) v (Pi.single a 1) = v a :=
  by
    classical
    change (((Pi.basisFun K (ReducedMono n q d)).constr K) v) (Pi.single a 1) = v a
    rw [← Pi.basisFun_apply]
    exact (Pi.basisFun K (ReducedMono n q d)).constr_basis K v a

private lemma dc_coeffFunctional {K : Type*} [Field K] {n q d : ℕ}
    (a : ReducedMono n q d) : dc (n := n) (q := q) (d := d) (Pi.single a 1) = coeffFunctional (K := K) q d a.toFinsupp := by
  apply (Pi.basisFun K (ReducedMono n q d)).ext
  intro b
  simp only [Pi.basisFun_apply, coeffFunctional, LinearMap.comp_apply, lcoeff_apply]
  change dc (n := n) (q := q) (d := d) (Pi.single a 1) (Pi.single b 1) = coeff a.toFinsupp (Rd.toPoly K n q d (Pi.single b 1))
  rw [dc_apply_single, toPoly_single, coeff_monomial]
  simp [Pi.single_apply, mono_injective.eq_iff, eq_comm]


private lemma span_image_generators {K F V J I : Type*} [Field K] [Field F]
    [Algebra K F] [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] (J → F)) (v : I → V) :
    Submodule.span F (Set.range fun x : Submodule.span K (Set.range v) => f x.val) =
      Submodule.span F (Set.range fun i => f (v i)) := by
  let W := Submodule.span K (Set.range v)
  let N := Submodule.span F (Set.range fun i => f (v i))
  have hle : W ≤ (N.restrictScalars K).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact hle x.property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩, rfl⟩

private noncomputable def genericMap {K : Type*} [Field K] (n q D : ℕ) :
    Module.Dual K (Rd K n q D) →ₗ[K]
      (ReducedMono n q (D - 2) → FractionRing (MvPolynomial (Fin n) K)) where
  toFun ℓ β := algebraMap _ _ (genericEntry K n q D ℓ β)
  map_add' := by
    intro u v
    funext β
    simp only [genericEntry, LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib,
      Pi.add_apply]
  map_smul' := by
    intro c u
    funext β
    have he : genericEntry K n q D (c • u) β = C c * genericEntry K n q D u β := by
      simp only [genericEntry, LinearMap.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, mul_assoc]
    change algebraMap (MvPolynomial (Fin n) K) (FractionRing (MvPolynomial (Fin n) K))
      (genericEntry K n q D (c • u) β) = c • _
    rw [he, map_mul, Algebra.smul_def]
    rfl


private lemma rank_on_span {K V I J : Type*} [Field K] [Fintype I] [Fintype J]
    [DecidableEq J] [AddCommGroup V] [Module K V]
    (v : I → V) (T : V →ₗ[K] Module.Dual K (J → K)) :
    (Matrix.of fun i j => T (v i) (Pi.single j 1)).rank =
      Module.finrank K (LinearMap.range (T.domRestrict (Submodule.span K (Set.range v)))) := by
  classical
  let E := RankProof.dualCoords (K := K) J
  have hspan : Submodule.span K (Set.range fun i j => T (v i) (Pi.single j 1)) =
      (LinearMap.range (T.domRestrict (Submodule.span K (Set.range v)))).map E := by
    rw [LinearMap.range_domRestrict, ← Submodule.map_comp, Submodule.map_span,
      ← Set.range_comp]
    rfl
  calc
    _ = Module.finrank K (Submodule.span K (Set.range fun i j => T (v i) (Pi.single j 1))) :=
      Matrix.rank_eq_finrank_span_row (Matrix.of fun i j => T (v i) (Pi.single j 1))
    _ = Module.finrank K ((LinearMap.range (T.domRestrict
        (Submodule.span K (Set.range v)))).map E) := congrArg (fun U : Submodule K (J → K) => Module.finrank K U) hspan
    _ = _ := (Submodule.equivMapOfInjective E (RankProof.dualCoords_injective J) _).finrank_eq.symm

private noncomputable def genMatrix {K I : Type*} [Field K] (n q D : ℕ)
    (v : I → Module.Dual K (Rd K n q D)) :
    Matrix I (ReducedMono n q (D - 2)) (MvPolynomial (Fin n) K) :=
  fun i β => genericEntry K n q D (v i) β

private lemma genMatrix_rank {K I : Type*} [Field K] [Fintype I] (n q D : ℕ)
    (v : I → Module.Dual K (Rd K n q D)) :
    ((genMatrix n q D v).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank =
      symbolicRank K n q D (Submodule.span K (Set.range v)) := by
  let F := FractionRing (MvPolynomial (Fin n) K)
  calc
    _ = Module.finrank F (Submodule.span F
        (Set.range fun i => genericMap (K := K) n q D (v i))) :=
      Matrix.rank_eq_finrank_span_row ((genMatrix n q D v).map (algebraMap _ F))
    _ = Module.finrank F (Submodule.span F
        (Set.range fun x : Submodule.span K (Set.range v) => genericMap (K := K) n q D x.val)) :=
      congrArg (fun U : Submodule F (ReducedMono n q (D - 2) → F) => Module.finrank F U)
        (span_image_generators (genericMap (K := K) n q D) v).symm
    _ = _ := rfl


private lemma genMatrix_eval_rank {K I : Type*} [Field K] [Fintype I] (n q D : ℕ)
    (v : I → Module.Dual K (Rd K n q D)) (a : Fin n → K) :
    ((genMatrix n q D v).map (eval a)).rank =
      Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict
        (Submodule.span K (Set.range v)))) := by
  have he : (genMatrix n q D v).map (eval a) =
      Matrix.of (fun i β => contraction K n q D a (v i) (Pi.single β 1)) := by
    ext i β
    exact RankProof.eval_generic q n D a (v i) β
  rw [he]
  exact rank_on_span v (contraction K n q D a)

private lemma span_basis_vals {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) [FiniteDimensional K W] :
    Submodule.span K (Set.range fun i => ((Module.finBasis K W) i).val) = W := by
  have h := Submodule.map_span W.subtype (Set.range (Module.finBasis K W))
  rw [← Set.range_comp, (Module.finBasis K W).span_eq, Submodule.map_top,
    Submodule.range_subtype] at h
  exact h.symm

private lemma special_rank_le {K : Type*} [Field K] (n q D : ℕ)
    (W : Submodule K (Module.Dual K (Rd K n q D))) (a : Fin n → K) :
    Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict W)) ≤
      symbolicRank K n q D W := by
  letI : Module.Free K W := Module.Free.of_divisionRing K W
  let v : Fin (Module.finrank K W) → Module.Dual K (Rd K n q D) :=
    fun i => ((Module.finBasis K W) i).val
  have hs : Submodule.span K (Set.range v) = W := span_basis_vals W
  have h := rank_specialization (genMatrix n q D v) a
  rw [genMatrix_eval_rank, genMatrix_rank, hs] at h
  exact h

private lemma exists_special_rank {K : Type*} [Field K] [Infinite K] (n q D : ℕ)
    (W : Submodule K (Module.Dual K (Rd K n q D))) :
    ∃ a : Fin n → K,
      Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict W)) =
        symbolicRank K n q D W := by
  letI : Module.Free K W := Module.Free.of_divisionRing K W
  let v : Fin (Module.finrank K W) → Module.Dual K (Rd K n q D) :=
    fun i => ((Module.finBasis K W) i).val
  have hs : Submodule.span K (Set.range v) = W := span_basis_vals W
  obtain ⟨a, ha⟩ := generic_rank_attained (genMatrix n q D v)
  rw [genMatrix_eval_rank, genMatrix_rank, hs] at ha
  exact ⟨a, ha⟩

private lemma symbolicRank_le_iff {K : Type*} [Field K] [Infinite K] (n q D : ℕ)
    (W : Submodule K (Module.Dual K (Rd K n q D))) (r : ℕ) :
    symbolicRank K n q D W ≤ r ↔ ∀ a : Fin n → K,
      Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict W)) ≤ r := by
  constructor
  · intro h a
    exact (special_rank_le n q D W a).trans h
  · intro h
    obtain ⟨a, ha⟩ := exists_special_rank n q D W
    rw [← ha]
    exact h a


private noncomputable def dualAct {K : Type*} [Field K] {n : ℕ} (q D : ℕ)
    (G : Matrix (Fin n) (Fin n) K) :
    Module.Dual K (Rd K n q D) →ₗ[K] Module.Dual K (Rd K n q D) :=
  (subG q G D).dualMap

private lemma action_special_rank_le {K : Type*} [Field K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hD : 2 ≤ D)
    (G : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Module.Dual K (Rd K n q D))) (a : Fin n → K) :
    Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict
      (W.map (dualAct q D G)))) ≤
    Module.finrank K (LinearMap.range ((contraction K n q D (G.mulVec a)).domRestrict W)) := by
  have he : (contraction K n q D a).comp (dualAct q D G) =
      (dualAct q (D - 2) G).comp (contraction K n q D (G.mulVec a)) := by
    apply LinearMap.ext
    intro ℓ
    exact contraction_covariance q hD G a ℓ
  have hr : LinearMap.range ((contraction K n q D a).domRestrict (W.map (dualAct q D G))) =
      (LinearMap.range ((contraction K n q D (G.mulVec a)).domRestrict W)).map
        (dualAct q (D - 2) G) := by
    simp only [LinearMap.range_domRestrict, ← Submodule.map_comp]
    rw [he]
  exact (congrArg (fun U : Submodule K (Module.Dual K (Rd K n q (D - 2))) =>
    Module.finrank K U) hr).trans_le (Submodule.finrank_map_le _ _)

private lemma action_symbolic_rank_le {K : Type*} [Field K] [Infinite K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hD : 2 ≤ D)
    (G : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Module.Dual K (Rd K n q D))) :
    symbolicRank K n q D (W.map (dualAct q D G)) ≤ symbolicRank K n q D W := by
  apply (symbolicRank_le_iff n q D _ _).mpr
  intro a
  exact (action_special_rank_le q hD G W a).trans (special_rank_le n q D W _)

private lemma symbolic_rank_mono {K : Type*} [Field K] (n q D : ℕ)
    {U W : Submodule K (Module.Dual K (Rd K n q D))} (h : U ≤ W) :
    symbolicRank K n q D U ≤ symbolicRank K n q D W := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨ℓ, rfl⟩
  exact ⟨⟨ℓ.val, h ℓ.property⟩, rfl⟩

private noncomputable def cSpan {K I : Type*} [Field K] [Fintype I] (A : Finset I) :
    Submodule K (I → K) := by
  classical
  exact Submodule.span K (Set.range fun i : A => (Pi.basisFun K I) i.val)

private lemma cSpan_finrank {K I : Type*} [Field K] [Fintype I] (A : Finset I) :
    Module.finrank K (cSpan (K := K) A) = A.card := by
  classical
  have hi := (Pi.basisFun K I).linearIndependent.comp (fun i : A => i.val) Subtype.val_injective
  simpa only [Function.comp_def, cSpan, Fintype.card_coe] using finrank_span_eq_card hi

private lemma cSpan_mem {K I : Type*} [Field K] [Fintype I] (A : Finset I) (v : I → K) :
    v ∈ cSpan (K := K) A ↔ ∀ j, j ∉ A → v j = 0 := by
  classical
  constructor
  · intro hv j hj
    have hle : cSpan (K := K) A ≤ LinearMap.ker (LinearMap.proj j) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp [LinearMap.mem_ker, Pi.basisFun_apply, Pi.single_apply, show j ≠ i.val from fun h => hj (h ▸ i.property)]
    exact hle hv
  · intro h
    have he : (∑ i : A, v i.val • ((Pi.basisFun K I) i.val : I → K)) = v := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.basisFun_apply]
      by_cases hj : j ∈ A
      · rw [Finset.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro i _ hi
          simp [Pi.single_apply, show i.val ≠ j from fun he => hi (Subtype.ext he)]
        · simp
      · simp [Pi.single_apply, show ∀ i : A, i.val ≠ j from fun i he => hj (he ▸ i.property), h j hj]
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma dc_basis_coeffFunctional {K : Type*} [Field K] {n q D : ℕ}
    (i : ReducedMono n q D) :
    dc (K := K) (n := n) (q := q) (d := D) ((Pi.basisFun K (ReducedMono n q D)) i) =
      coeffFunctional (K := K) q D i.toFinsupp := by
  classical
  rw [Pi.basisFun_apply]
  exact dc_coeffFunctional (K := K) (n := n) (q := q) (d := D) i

private lemma cSpan_monomialSpan {K : Type*} [Field K] {n q D : ℕ}
    (A : Finset (ReducedMono n q D)) :
    (cSpan (K := K) A).map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap =
      monomialSpan (K := K) q D (A.image ReducedMono.toFinsupp) := by
  classical
  unfold cSpan monomialSpan
  rw [Submodule.map_span]
  congr 1
  ext ℓ
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.val.toFinsupp, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩,
      (dc_basis_coeffFunctional (K := K) i.val).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(Pi.basisFun K (ReducedMono n q D)) i, ⟨⟨i, hi⟩, rfl⟩,
      dc_basis_coeffFunctional (K := K) i⟩


private noncomputable def coordProj {K I : Type*} [Field K] (A : Finset I) :
    (I → K) →ₗ[K] (A → K) := LinearMap.pi fun a => LinearMap.proj a.val

private lemma upper_projected_independent {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (A : Finset I) (u : A → I → K)
    (hd : ∀ a, u a a.val ≠ 0) (hu : ∀ a j, w j < w a.val → u a j = 0) :
    LinearIndependent K ((coordProj (K := K) A) ∘ u) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hi
  let S : Finset A := Finset.univ.filter (fun j => c j ≠ 0)
  obtain ⟨k, hk, hmin⟩ := S.exists_min_image (fun j => w j.val) ⟨i, by simp [S, hi]⟩
  have hkn : c k ≠ 0 := (Finset.mem_filter.mp hk).2
  have he := congrFun hc k
  change (∑ j : A, c j • (coordProj A (u j))) k = 0 at he
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  have hs : (∑ j : A, c j * u j k.val) = c k * u k k.val := by
    rw [Finset.sum_eq_single k]
    · intro j _ hj
      by_cases hz : c j = 0
      · rw [hz, zero_mul]
      · have hle := hmin j (by simp [S, hz])
        have hne : w k.val ≠ w j.val := fun h => hj (Subtype.ext (hw h.symm))
        rw [hu j k.val (lt_of_le_of_ne hle hne), mul_zero]
    · simp
  exact mul_ne_zero hkn (hd k) (hs.symm.trans he)

private lemma upper_initial_eq {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (A : Finset I) (u : A → I → K)
    (hd : ∀ a, u a a.val ≠ 0) (hu : ∀ a j, w j < w a.val → u a j = 0)
    (hweight : ∑ b ∈ initialFamily w (Submodule.span K (Set.range u)), w b ≤ ∑ a ∈ A, w a) :
    initialFamily w (Submodule.span K (Set.range u)) = A := by
  classical
  let W := Submodule.span K (Set.range u)
  let B := initialFamily w W
  let P := coordProj (K := K) A
  have hproj := upper_projected_independent w hw A u hd hu
  have hind : LinearIndependent K u := LinearIndependent.of_comp P hproj
  have hdim : Module.finrank K W = A.card := by
    exact (finrank_span_eq_card hind).trans (Fintype.card_coe A)
  have hcard : B.card = A.card := (initialFamily_card w hw W).trans hdim
  let e : A ≃ B := Fintype.equivOfCardEq (by simpa using hcard.symm)
  have hdis : Disjoint W (LinearMap.ker P) := Submodule.range_ker_disjoint hproj
  have hBi : LinearIndependent K (P ∘ initialRows w W) :=
    (initialRows_independent w hw W).map (by rw [initialRows_span w hw W]; exact hdis)
  let M : Matrix A A K := fun i j => initialRows w W (e i) j.val
  have hMi : LinearIndependent K M.row := hBi.comp e e.injective
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hMi)).ne_zero
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hprod : ∏ a : A, M (σ a) a ≠ 0 := right_ne_zero_of_mul hσ
  have hentry (a : A) : M (σ a) a ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) a (Finset.mem_univ a)
  have hle (a : A) : w a.val ≤ w (e (σ a)).val := by
    by_contra h
    exact hentry a ((initialRows_properties w W (e (σ a))).2.2 a.val (by omega))
  have hsum : (∑ a : A, w (e (σ a)).val) = ∑ b ∈ B, w b := by
    exact (Equiv.sum_comp σ (fun a => w (e a).val)).trans
      ((Equiv.sum_comp e (fun b => w b.val)).trans (Finset.sum_coe_sort B w))
  have heq (a : A) : w a.val = w (e (σ a)).val := by
    by_contra h
    have hs := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset A)) => hle j)
      ⟨a, Finset.mem_univ a, lt_of_le_of_ne (hle a) h⟩
    rw [hsum, Finset.sum_coe_sort A w] at hs
    exact Nat.not_lt_of_ge hweight hs
  have hval (a : A) : (e (σ a)).val = a.val := hw (heq a).symm
  change B = A
  apply Finset.ext
  intro j
  constructor
  · intro hj
    let b : B := ⟨j, hj⟩
    obtain ⟨a, ha⟩ := (e.surjective.comp σ.surjective) b
    change e (σ a) = b at ha
    have h : j = a.val := (congrArg Subtype.val ha).symm.trans (hval a)
    rw [h]
    exact a.property
  · intro hj
    let a : A := ⟨j, hj⟩
    have h : (e (σ a)).val = j := hval a
    rw [← h]
    exact (e (σ a)).property


private lemma upper_span_bound {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (A : Finset I) (u : A → I → K)
    (hd : ∀ a, u a a.val ≠ 0) (hu : ∀ a j, w j < w a.val → u a j = 0)
    (v : I → K) (hv : v ∈ Submodule.span K (Set.range u)) (d : ℕ)
    (hz : ∀ a : A, w a.val < d → v a.val = 0) : ∀ j, w j < d → v j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hcz (a : A) (ha : w a.val < d) : c a = 0 := by
    by_contra hca
    let S : Finset A := Finset.univ.filter (fun j => c j ≠ 0)
    obtain ⟨k, hk, hmin⟩ := S.exists_min_image (fun j => w j.val) ⟨a, by simp [S, hca]⟩
    have hkn : c k ≠ 0 := (Finset.mem_filter.mp hk).2
    have hkd : w k.val < d := (hmin a (by simp [S, hca])).trans_lt ha
    have he := congrFun hc k.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz k hkd] at he
    have hs : (∑ j : A, c j * u j k.val) = c k * u k k.val := by
      rw [Finset.sum_eq_single k]
      · intro j _ hj
        by_cases hcj : c j = 0
        · rw [hcj, zero_mul]
        · have hle := hmin j (by simp [S, hcj])
          rw [hu j k.val (lt_of_le_of_ne hle (fun h => hj (Subtype.ext (hw h.symm)))), mul_zero]
      · simp
    exact mul_ne_zero hkn (hd k) (hs.symm.trans he)
  intro j hj
  rw [← hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : w a.val < d
  · rw [hcz a ha, zero_mul]
  · rw [hu a j (by omega), mul_zero]

private lemma lower_span_bound {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (A : Finset I) (u : A → I → K)
    (hd : ∀ a, u a a.val ≠ 0) (hu : ∀ a j, w a.val < w j → u a j = 0)
    (v : I → K) (hv : v ∈ Submodule.span K (Set.range u)) (d : ℕ)
    (hz : ∀ a : A, d < w a.val → v a.val = 0) : ∀ j, d < w j → v j = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  have hcz (a : A) (ha : d < w a.val) : c a = 0 := by
    by_contra hca
    let S : Finset A := Finset.univ.filter (fun j => c j ≠ 0)
    obtain ⟨k, hk, hmax⟩ := S.exists_max_image (fun j => w j.val) ⟨a, by simp [S, hca]⟩
    have hkn : c k ≠ 0 := (Finset.mem_filter.mp hk).2
    have hkd : d < w k.val := ha.trans_le (hmax a (by simp [S, hca]))
    have he := congrFun hc k.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hz k hkd] at he
    have hs : (∑ j : A, c j * u j k.val) = c k * u k k.val := by
      rw [Finset.sum_eq_single k]
      · intro j _ hj
        by_cases hcj : c j = 0
        · rw [hcj, zero_mul]
        · have hle := hmax j (by simp [S, hcj])
          rw [hu j k.val (lt_of_le_of_ne hle (fun h => hj (Subtype.ext (hw h)))), mul_zero]
      · simp
    exact mul_ne_zero hkn (hd k) (hs.symm.trans he)
  intro j hj
  rw [← hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : d < w a.val
  · rw [hcz a ha, zero_mul]
  · rw [hu a j (by omega), mul_zero]

private lemma upper_initial_span_eq {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (A : Finset I) (u : A → I → K)
    (hd : ∀ a, u a a.val ≠ 0) (hu : ∀ a j, w j < w a.val → u a j = 0)
    (hweight : ∑ b ∈ initialFamily w (Submodule.span K (Set.range u)), w b ≤ ∑ a ∈ A, w a) :
    Submodule.span K (Set.range u) = cSpan (K := K) A := by
  classical
  let W := Submodule.span K (Set.range u)
  have hA : initialFamily w W = A := upper_initial_eq w hw A u hd hu hweight
  let P := (coordProj (K := K) A).domRestrict W
  have hdis : Disjoint W (LinearMap.ker (coordProj (K := K) A)) :=
    Submodule.range_ker_disjoint (upper_projected_independent w hw A u hd hu)
  have hPinj : Function.Injective P := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    apply Subtype.ext
    apply hdis.le_bot
    exact ⟨v.property, hv⟩
  have hind : LinearIndependent K u := LinearIndependent.of_comp (coordProj A)
    (upper_projected_independent w hw A u hd hu)
  have hdim : Module.finrank K W = Module.finrank K (A → K) := by
    simpa using finrank_span_eq_card hind
  have hsurj : Function.Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hPinj
  have hsingle (i : A) : (Pi.basisFun K I) i.val ∈ W := by
    obtain ⟨v, hv⟩ := hsurj ((Pi.basisFun K A) i)
    have hval (a : A) : v.val a.val = if a = i then 1 else 0 := by
      have hh := congrFun hv a
      simpa only [P, coordProj, LinearMap.domRestrict_apply, LinearMap.pi_apply,
        LinearMap.proj_apply, Pi.basisFun_apply, Pi.single_apply] using hh
    have hlow : ∀ j, w j < w i.val → v.val j = 0 :=
      upper_span_bound w hw A u hd hu v.val v.property (w i.val) (by
        intro a ha
        rw [hval a, if_neg (fun he => by subst a; omega)])
    have hhigh : ∀ j, w i.val < w j → v.val j = 0 := by
      have hmem : v.val ∈ Submodule.span K (Set.range (initialRows w W)) := by
        rw [initialRows_span w hw W]; exact v.property
      exact lower_span_bound w hw (initialFamily w W) (initialRows w W)
        (fun a => (initialRows_properties w W a).2.1 ▸ one_ne_zero)
        (fun a j hj => (initialRows_properties w W a).2.2 j hj)
        v.val hmem (w i.val) (by
          intro a ha
          let a' : A := ⟨a.val, hA ▸ a.property⟩
          have hh := hval a'
          rw [if_neg (fun he => by have := congrArg (fun b : A => w b.val) he; dsimp [a'] at this; omega)] at hh
          exact hh)
    have he : v.val = (Pi.basisFun K I) i.val := by
      funext j
      by_cases hij : j = i.val
      · subst j
        simpa only [Pi.basisFun_apply, Pi.single_apply, if_pos rfl] using hval i
      · have hne : w j ≠ w i.val := fun h => hij (hw h)
        rcases lt_or_gt_of_ne hne with hj | hj
        · simp [Pi.basisFun_apply, Pi.single_apply, hij, Ne.symm hij, hlow j hj]
        · simp [Pi.basisFun_apply, Pi.single_apply, hij, Ne.symm hij, hhigh j hj]
    exact he ▸ v.property
  have hle : cSpan (K := K) A ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hsingle i
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [cSpan_finrank]
  exact (finrank_span_eq_card hind).trans (Fintype.card_coe A) |>.symm


open scoped Pointwise

private def lowerPoly {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ a ∈ p.support, Finsupp.weight w a < d

private def boundedPoly {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → ℕ) (d : ℕ) (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ a ∈ p.support, Finsupp.weight w a ≤ d

private def leadForm {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → ℕ) (p : MvPolynomial (Fin n) K) (a : Fin n →₀ ℕ) (c : K) : Prop :=
  lowerPoly w (Finsupp.weight w a) (p - monomial a c)

private lemma lowerPoly_zero {K : Type*} [Field K] {n : ℕ} (w : Fin n → ℕ) (d : ℕ) :
    lowerPoly (K := K) w d 0 := by simp [lowerPoly]

private lemma lowerPoly_add {K : Type*} [Field K] {n d : ℕ} {w : Fin n → ℕ}
    {p r : MvPolynomial (Fin n) K} (hp : lowerPoly w d p) (hr : lowerPoly w d r) :
    lowerPoly w d (p + r) := by
  intro a ha
  rcases Finset.mem_union.mp (support_add ha) with ha | ha
  · exact hp a ha
  · exact hr a ha

private lemma lowerPoly_sum {K I : Type*} [Field K] {n d : ℕ} {w : Fin n → ℕ}
    (s : Finset I) (f : I → MvPolynomial (Fin n) K) (h : ∀ i ∈ s, lowerPoly w d (f i)) :
    lowerPoly w d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerPoly_zero (K := K) w d
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact lowerPoly_add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private lemma lowerPoly_mul {K : Type*} [Field K] {n d e : ℕ} {w : Fin n → ℕ}
    {p r : MvPolynomial (Fin n) K} (hp : lowerPoly w d p) (hr : boundedPoly w e r) :
    lowerPoly w (d + e) (p * r) := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]
  exact Nat.add_lt_add_of_lt_of_le (hp b hb) (hr c hc)

private lemma bounded_monomial {K : Type*} [Field K] {n : ℕ} (w : Fin n → ℕ)
    (a : Fin n →₀ ℕ) (c : K) : boundedPoly w (Finsupp.weight w a) (monomial a c) := by
  intro b hb
  have he := Finset.mem_singleton.mp (support_monomial_subset hb)
  subst b
  exact le_rfl

private lemma leadForm_bound {K : Type*} [Field K] {n : ℕ} {w : Fin n → ℕ}
    {p : MvPolynomial (Fin n) K} {a : Fin n →₀ ℕ} {c : K} (hp : leadForm w p a c) :
    boundedPoly w (Finsupp.weight w a) p := by
  intro b hb
  have he : p = (p - monomial a c) + monomial a c := by ring
  rw [he] at hb
  rcases Finset.mem_union.mp (support_add hb) with hb | hb
  · exact (hp b hb).le
  · exact bounded_monomial w a c b hb

private lemma leadForm_mul {K : Type*} [Field K] {n : ℕ} {w : Fin n → ℕ}
    {p r : MvPolynomial (Fin n) K} {a b : Fin n →₀ ℕ} {c e : K}
    (hp : leadForm w p a c) (hr : leadForm w r b e) :
    leadForm w (p * r) (a + b) (c * e) := by
  have h1 := lowerPoly_mul hp (leadForm_bound hr)
  have h2 := lowerPoly_mul hr (bounded_monomial w a c)
  have hh := lowerPoly_add h1 (by simpa only [add_comm] using h2)
  have he : p * r - monomial (a + b) (c * e) =
      (p - monomial a c) * r + (r - monomial b e) * monomial a c := by
    rw [← monomial_mul]
    ring
  unfold leadForm
  rw [map_add, he]
  exact hh

private lemma leadForm_pow {K : Type*} [Field K] {n : ℕ} {w : Fin n → ℕ}
    {p : MvPolynomial (Fin n) K} {a : Fin n →₀ ℕ} {c : K}
    (hp : leadForm w p a c) (m : ℕ) : leadForm w (p ^ m) (m • a) (c ^ m) := by
  induction m with
  | zero => simp only [pow_zero, zero_smul, leadForm, ← C_apply, map_one, sub_self]; exact lowerPoly_zero (K := K) w _
  | succ m ih => simpa only [pow_succ, succ_nsmul] using leadForm_mul ih hp

private lemma leadForm_prod {K I : Type*} [Field K] {n : ℕ} {w : Fin n → ℕ}
    (s : Finset I) (p : I → MvPolynomial (Fin n) K) (a : I → Fin n →₀ ℕ) (c : I → K)
    (hp : ∀ i ∈ s, leadForm w (p i) (a i) (c i)) :
    leadForm w (∏ i ∈ s, p i) (∑ i ∈ s, a i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, leadForm, ← C_apply, map_one, sub_self]; exact lowerPoly_zero (K := K) w _
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact leadForm_mul (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

private lemma borel_leadForm {K : Type*} [Field K] {n : ℕ} (w : Fin n → ℕ)
    (hw : StrictAnti w) (g : Fin n → MvPolynomial (Fin n) K) (hg : IsBorel g) :
    ∃ a : Fin n → K, (∀ j, a j ≠ 0) ∧ ∀ j, leadForm w (g j) (Finsupp.single j 1) (a j) := by
  classical
  choose a ha c hc using hg
  refine ⟨a, ha, ?_⟩
  intro j
  unfold leadForm
  rw [hc j, C_mul_X_eq_monomial, add_sub_cancel_left]
  apply lowerPoly_sum
  intro i hi
  rw [C_mul_X_eq_monomial]
  intro b hb
  have he := Finset.mem_singleton.mp (support_monomial_subset hb)
  subst b
  simpa only [Finsupp.weight_single, one_smul] using hw (Finset.mem_filter.mp hi).2

private lemma borel_monomial_lead {K : Type*} [Field K] {n : ℕ} (w : Fin n → ℕ)
    (hw : StrictAnti w) (g : Fin n → MvPolynomial (Fin n) K) (hg : IsBorel g)
    (b : Fin n →₀ ℕ) :
    ∃ c : K, c ≠ 0 ∧ leadForm w (aeval (R := K) g (monomial b 1)) b c := by
  classical
  obtain ⟨a, ha, hlead⟩ := borel_leadForm w hw g hg
  refine ⟨∏ j : Fin n, (a j) ^ b j, Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (ha j)), ?_⟩
  have hprod := leadForm_prod Finset.univ (fun j => (g j) ^ b j)
    (fun j => b j • Finsupp.single j 1) (fun j => (a j) ^ b j)
    (fun j _ => leadForm_pow (hlead j) (b j))
  have he : (∑ j : Fin n, b j • Finsupp.single j 1) = b := by
    ext j
    simp
  rw [he] at hprod
  rw [aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun j => pow_zero (g j))]
  exact hprod

private lemma leadForm_coeff {K : Type*} [Field K] {n : ℕ} {w : Fin n → ℕ}
    {p : MvPolynomial (Fin n) K} {a : Fin n →₀ ℕ} {c : K}
    (hp : leadForm w p a c) {b : Fin n →₀ ℕ}
    (hb : Finsupp.weight w a ≤ Finsupp.weight w b) :
    coeff b p = if b = a then c else 0 := by
  have he : coeff b (p - monomial a c) = 0 := by
    by_contra h
    exact Nat.not_lt_of_ge hb (hp b (mem_support_iff.mpr h))
  rw [coeff_sub, sub_eq_zero, coeff_monomial] at he
  simpa only [eq_comm] using he


private def varWeight (q n : ℕ) (j : Fin n) : ℕ := q ^ j.rev.val

private noncomputable def monWeight {n q d : ℕ} (a : ReducedMono n q d) : ℕ :=
  Finsupp.weight (varWeight q n) a.toFinsupp

private lemma digits_sum (q n : ℕ) (f : Fin n → ℕ) :
    (∑ j : Fin n, q ^ j.val * f j) = Nat.ofDigits q (List.ofFn f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    rw [← ih (fun j => f j.succ), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

private lemma monWeight_digits {n q d : ℕ} (a : ReducedMono n q d) :
    monWeight a = Nat.ofDigits q (List.ofFn fun j => (a.val j.rev : ℕ)) := by
  calc
    _ = ∑ j : Fin n, (a.val j : ℕ) * q ^ j.rev.val := by
      simp only [monWeight, Finsupp.weight_eq_sum, smul_eq_mul, varWeight,
        ReducedMono.toFinsupp]
      rfl
    _ = ∑ j : Fin n, q ^ j.val * (a.val j.rev : ℕ) := by
      simpa only [Fin.revPerm_apply, Fin.rev_rev, mul_comm] using
        (Equiv.sum_comp (Fin.revPerm (n := n))
          (fun j => (a.val j : ℕ) * q ^ j.rev.val)).symm
    _ = _ := digits_sum q n _

private lemma monWeight_injective {n q d : ℕ} (hq : 1 < q) :
    Function.Injective (monWeight : ReducedMono n q d → ℕ) := by
  intro a b hab
  rw [monWeight_digits, monWeight_digits] at hab
  have he := Nat.ofDigits_inj_of_len_eq hq (by simp :
      (List.ofFn fun j => (a.val j.rev : ℕ)).length =
        (List.ofFn fun j => (b.val j.rev : ℕ)).length)
    (by intro k hk; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk; exact (a.val j.rev).isLt)
    (by intro k hk; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk; exact (b.val j.rev).isLt) hab
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hh := congrFun (List.ofFn_injective he) j.rev
  simpa only [Fin.rev_rev] using hh

private lemma varWeight_anti {q n : ℕ} (hq : 1 < q) : StrictAnti (varWeight q n) := by
  intro i j hij
  apply Nat.pow_lt_pow_right hq
  exact Fin.rev_lt_rev.mpr hij

private lemma dc_symm_apply {K : Type*} [Field K] {n q d : ℕ}
    (ℓ : Module.Dual K (Rd K n q d)) (a : ReducedMono n q d) :
    (dc (K := K) (n := n) (q := q) (d := d)).symm ℓ a =
      ℓ ((Pi.basisFun K (ReducedMono n q d)) a) := rfl

private noncomputable def coordSub {K : Type*} [Field K] {n : ℕ} (q D : ℕ)
    (g : Fin n → MvPolynomial (Fin n) K) :
    (ReducedMono n q D → K) →ₗ[K] (ReducedMono n q D → K) :=
  (dc (K := K) (n := n) (q := q) (d := D)).symm.toLinearMap.comp
    ((substR q g D).dualMap.comp (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap)

private lemma coordSub_entry {K : Type*} [Field K] {n q D : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (a b : ReducedMono n q D) :
    coordSub q D g ((Pi.basisFun K (ReducedMono n q D)) a) b =
      coeff a.toFinsupp (aeval (R := K) g (monomial b.toFinsupp 1)) := by
  simp only [coordSub, LinearMap.comp_apply, LinearEquiv.coe_coe, dc_symm_apply,
    dc_basis_coeffFunctional, LinearMap.dualMap_apply', substR, coeffFunctional,
    LinearMap.comp_apply, lcoeff_apply, toPoly_coeff]
  rw [Pi.basisFun_apply, toPoly_single]
  simp only [Rd.ofPoly, LinearMap.pi_apply, lcoeff_apply, AlgHom.toLinearMap_apply]

private lemma coordSub_triangular {K : Type*} [Field K] {n q D : ℕ} (hq : 1 < q)
    (g : Fin n → MvPolynomial (Fin n) K) (hg : IsBorel g) :
    (∀ a : ReducedMono n q D, coordSub q D g ((Pi.basisFun K _) a) a ≠ 0) ∧
    ∀ a b : ReducedMono n q D, monWeight b < monWeight a →
      coordSub q D g ((Pi.basisFun K _) a) b = 0 := by
  constructor
  · intro a
    obtain ⟨c, hc, hlead⟩ := borel_monomial_lead (varWeight q n) (varWeight_anti hq) g hg a.toFinsupp
    rw [coordSub_entry, leadForm_coeff hlead le_rfl, if_pos rfl]
    exact hc
  · intro a b hab
    obtain ⟨c, _, hlead⟩ := borel_monomial_lead (varWeight q n) (varWeight_anti hq) g hg b.toFinsupp
    rw [coordSub_entry, leadForm_coeff hlead hab.le]
    rw [if_neg (fun h => by have he := mono_injective h; subst a; exact Nat.lt_irrefl _ hab)]


private lemma aeval_diagonal_monomial {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) (b : Fin n →₀ ℕ) :
    aeval (R := K) (fun j => C (a j) * X j) (monomial b 1) =
      (∏ j : Fin n, a j ^ b j) • (monomial b 1 : MvPolynomial (Fin n) K) := by
  classical
  rw [aeval_monomial]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _)]
  simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod]
  rw [Algebra.smul_def, algebraMap_eq, monomial_eq]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _)]

private lemma diagonal_coordSub {K : Type*} [Field K] {n q D : ℕ}
    (a : Fin n → K) (v : ReducedMono n q D → K) (b : ReducedMono n q D) :
    coordSub q D (fun j => C (a j) * X j) v b =
      (∏ j : Fin n, a j ^ (b.val j : ℕ)) * v b := by
  have hv : (∑ i : ReducedMono n q D, v i • (Pi.basisFun K _) i) = v := by
    simpa only [Pi.basisFun_repr] using (Pi.basisFun K (ReducedMono n q D)).sum_repr v
  have he (i : ReducedMono n q D) :
      coordSub q D (fun j => C (a j) * X j) ((Pi.basisFun K _) i) b =
        if i = b then ∏ j, a j ^ (b.val j : ℕ) else 0 := by
    rw [coordSub_entry, aeval_diagonal_monomial]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases hi : i = b
    · subst i
      simp only [if_true, mul_one]
      rfl
    · have hn : b.toFinsupp ≠ i.toFinsupp := fun h => hi (mono_injective h).symm
      simp only [if_neg hi, if_neg hn, mul_zero]
  calc
    _ = coordSub q D (fun j => C (a j) * X j)
        (∑ i : ReducedMono n q D, v i • (Pi.basisFun K _) i) b :=
      congrArg (fun x => coordSub q D (fun j => C (a j) * X j) x b) hv.symm
    _ = ∑ i : ReducedMono n q D, v i *
        coordSub q D (fun j => C (a j) * X j) ((Pi.basisFun K _) i) b := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := by simp only [he]; simp [mul_comm]

private lemma linForm_diagonal {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) (j : Fin n) : linForm (cols (Matrix.diagonal a) j) = C (a j) * X j := by
  classical
  simp only [linForm, cols, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

private lemma polynomial_path_rank {K R I J : Type*} [Field K] [Infinite K]
    [Fintype R] [Fintype I] [Fintype J] [DecidableEq J]
    (p : Matrix R I (Polynomial K)) (T : (I → K) →ₗ[K] (J → K)) (r : ℕ)
    (h : ∀ t : K, t ≠ 0 →
      (Matrix.of fun i j => T (fun a => Polynomial.eval t (p i a)) j).rank ≤ r) :
    (Matrix.of fun i j => T (fun a => Polynomial.eval 0 (p i a)) j).rank ≤ r := by
  classical
  let M : Matrix R J (Polynomial K) := fun i j =>
    ∑ a : I, Polynomial.C (T ((Pi.basisFun K I) a) j) * p i a
  have he (t : K) : M.map (Polynomial.evalRingHom t) =
      Matrix.of (fun i j => T (fun a => Polynomial.eval t (p i a)) j) := by
    ext i j
    change Polynomial.eval t (∑ a : I, Polynomial.C (T ((Pi.basisFun K I) a) j) * p i a) = _
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
    have hs : (∑ a : I, Polynomial.eval t (p i a) • (Pi.basisFun K I) a) =
        (fun a => Polynomial.eval t (p i a)) := by
      simpa only [Pi.basisFun_repr] using
        (Pi.basisFun K I).sum_repr (fun a => Polynomial.eval t (p i a))
    change (∑ a : I, T ((Pi.basisFun K I) a) j * Polynomial.eval t (p i a)) =
      T (fun a => Polynomial.eval t (p i a)) j
    conv_rhs => rw [← hs]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hh := polynomial_rank_closed M r (by intro t ht; rw [he]; exact h t ht)
  rw [he] at hh
  exact hh

private noncomputable def initialPath {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (W : Submodule K (I → K)) :
    Matrix (initialFamily w W) I (Polynomial K) :=
  fun i a => Polynomial.C (initialRows w W i a) * Polynomial.X ^ (w i.val - w a)

private lemma initialPath_zero {K I : Type*} [Field K] [Fintype I]
    (w : I → ℕ) (hw : Function.Injective w) (W : Submodule K (I → K))
    (i : initialFamily w W) :
    (fun a => Polynomial.eval 0 (initialPath w W i a)) = (Pi.basisFun K I) i.val := by
  classical
  funext a
  simp only [initialPath, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Pi.basisFun_apply, Pi.single_apply]
  by_cases ha : a = i.val
  · subst a
    simp [(initialRows_properties w W i).2.1]
  · have hne : w a ≠ w i.val := fun h => ha (hw h)
    rcases lt_or_gt_of_ne hne with ha' | ha'
    · have hd : w i.val - w a ≠ 0 := by omega
      simp [ha, Ne.symm ha, hd]
    · simp [ha, Ne.symm ha, (initialRows_properties w W i).2.2 a ha']

private lemma initialPath_nonzero {K : Type*} [Field K] {n q D : ℕ}
    (W : Submodule K (ReducedMono n q D → K)) (t : K) (ht : t ≠ 0)
    (i : initialFamily monWeight W) :
    (fun a => Polynomial.eval t (initialPath monWeight W i a)) =
      t ^ monWeight i.val • coordSub q D
        (fun j => C (t⁻¹ ^ varWeight q n j) * X j) (initialRows monWeight W i) := by
  funext a
  rw [Pi.smul_apply, diagonal_coordSub]
  have hpow : (∏ j : Fin n, (t⁻¹ ^ varWeight q n j) ^ (a.val j : ℕ)) =
      t⁻¹ ^ monWeight a := by
    simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, monWeight, Finsupp.weight_eq_sum, smul_eq_mul,
      ReducedMono.toFinsupp]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
    rfl
  rw [hpow]
  simp only [initialPath, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  by_cases ha : monWeight a ≤ monWeight i.val
  · rw [pow_sub₀ t ht ha, inv_pow]
    ring
  · rw [(initialRows_properties monWeight W i).2.2 a (by omega), mul_zero, zero_mul, mul_zero]


private lemma dc_coordSub {K : Type*} [Field K] {n q D : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (v : ReducedMono n q D → K) :
    dc (K := K) (n := n) (q := q) (d := D) (coordSub q D g v) =
      (dc (K := K) (n := n) (q := q) (d := D) v).comp (substR q g D) := by
  exact (dc (K := K) (n := n) (q := q) (d := D)).apply_symm_apply _

private lemma contraction_family_rank_le {K R : Type*} [Field K] [Fintype R]
    (n q D : ℕ) (a : Fin n → K) (v : R → Module.Dual K (Rd K n q D))
    (W : Submodule K (Module.Dual K (Rd K n q D))) (hv : ∀ i, v i ∈ W) :
    (Matrix.of fun i β => contraction K n q D a (v i) (Pi.single β 1)).rank ≤
      symbolicRank K n q D W := by
  rw [rank_on_span]
  have hspan : Submodule.span K (Set.range v) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  apply le_trans _ (special_rank_le n q D W a)
  apply Submodule.finrank_mono
  simp only [LinearMap.range_domRestrict]
  exact Submodule.map_mono hspan

private lemma initial_symbolic_rank_le {K : Type*} [Field K] [Infinite K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hq : 1 < q) (hD : 2 ≤ D)
    (W : Submodule K (ReducedMono n q D → K)) :
    symbolicRank K n q D ((cSpan (K := K) (initialFamily monWeight W)).map
      (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) ≤
    symbolicRank K n q D (W.map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) := by
  classical
  let A := initialFamily (monWeight : ReducedMono n q D → ℕ) W
  let E := dc (K := K) (n := n) (q := q) (d := D)
  let U := W.map E.toLinearMap
  let r := symbolicRank K n q D U
  apply (symbolicRank_le_iff n q D _ r).mpr
  intro a
  let T : (ReducedMono n q D → K) →ₗ[K] (ReducedMono n q (D - 2) → K) :=
    (RankProof.dualCoords (K := K) _).comp ((contraction K n q D a).comp E.toLinearMap)
  have hh := polynomial_path_rank (initialPath monWeight W) T r (by
    intro t ht
    let b : Fin n → K := fun j => t⁻¹ ^ varWeight q n j
    let G := Matrix.diagonal b
    have hmem (i : A) :
        E (fun j => Polynomial.eval t (initialPath monWeight W i j)) ∈ U.map (dualAct q D G) := by
      rw [initialPath_nonzero W t ht i, map_smul, dc_coordSub]
      apply Submodule.smul_mem
      refine ⟨E (initialRows monWeight W i), ?_, ?_⟩
      · exact ⟨initialRows monWeight W i, (initialRows_properties monWeight W i).1, rfl⟩
      · change (E (initialRows monWeight W i)).comp (subG q G D) = _
        simp only [subG, linForm_diagonal, G, b]
        rfl
    have hle := contraction_family_rank_le n q D a
      (fun i : A => E (fun j => Polynomial.eval t (initialPath monWeight W i j)))
      (U.map (dualAct q D G)) hmem
    exact hle.trans (action_symbolic_rank_le q hD G U))
  have hz : (Matrix.of fun i β => T (fun j => Polynomial.eval 0 (initialPath monWeight W i j)) β) =
      Matrix.of (fun i : A => fun β => contraction K n q D a
        (E ((Pi.basisFun K _) i.val)) (Pi.single β 1)) := by
    ext i β
    change T (fun j => Polynomial.eval 0 (initialPath monWeight W i j)) β = _
    rw [initialPath_zero monWeight (monWeight_injective hq)]
    rfl
  rw [hz, rank_on_span] at hh
  have hs : Submodule.span K (Set.range fun i : A => E ((Pi.basisFun K _) i.val)) =
      (cSpan (K := K) A).map E.toLinearMap := by
    rw [cSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [hs] at hh
  exact hh

private lemma borel_matrix {K : Type*} [Field K] {n : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (hg : IsBorel g) :
    ∃ G : Matrix (Fin n) (Fin n) K, ∀ j, linForm (cols G j) = g j := by
  classical
  choose a ha c hc using hg
  let G : Matrix (Fin n) (Fin n) K := fun i j =>
    (if i = j then a j else 0) + (if j < i then c j i else 0)
  refine ⟨G, ?_⟩
  intro j
  rw [hc j]
  simp only [linForm, cols, G, map_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp_all


private lemma dc_map_coordSub {K : Type*} [Field K] {n q D : ℕ}
    (g : Fin n → MvPolynomial (Fin n) K) (W : Submodule K (ReducedMono n q D → K)) :
    (W.map (coordSub q D g)).map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap =
      (W.map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap).map
        (substR q g D).dualMap := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  exact dc_coordSub g v

private lemma coordSub_rank_le {K : Type*} [Field K] [Infinite K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hD : 2 ≤ D)
    (g : Fin n → MvPolynomial (Fin n) K) (hg : IsBorel g)
    (W : Submodule K (ReducedMono n q D → K)) :
    symbolicRank K n q D ((W.map (coordSub q D g)).map
      (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) ≤
    symbolicRank K n q D (W.map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) := by
  obtain ⟨G, hG⟩ := borel_matrix g hg
  have he : (fun j => linForm (cols G j)) = g := funext hG
  rw [dc_map_coordSub]
  have hh := action_symbolic_rank_le q hD G
    (W.map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap)
  simpa only [dualAct, subG, he] using hh

private lemma monomial_borel_replacement {K : Type*} [Field K] [Infinite K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hq : 1 < q) (hD : 2 ≤ D)
    (W : Submodule K (ReducedMono n q D → K)) :
    ∃ A : Finset (ReducedMono n q D),
      A.card = Module.finrank K W ∧
      IsBorelInvariant q D ((cSpan (K := K) A).map
        (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) ∧
      symbolicRank K n q D ((cSpan (K := K) A).map
        (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) ≤
      symbolicRank K n q D (W.map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap) := by
  classical
  let I := ReducedMono n q D
  let w : I → ℕ := monWeight
  have hw : Function.Injective w := monWeight_injective hq
  let E := dc (K := K) (n := n) (q := q) (d := D)
  let r := symbolicRank K n q D (W.map E.toLinearMap)
  let good : Finset (Finset I) := Finset.univ.filter fun A =>
    A.card = Module.finrank K W ∧
      symbolicRank K n q D ((cSpan (K := K) A).map E.toLinearMap) ≤ r
  have hnonempty : good.Nonempty := by
    refine ⟨initialFamily w W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨initialFamily_card w hw W, initial_symbolic_rank_le q hq hD W⟩
  obtain ⟨A, hAgood, hmax⟩ := good.exists_max_image (fun B => ∑ i ∈ B, w i) hnonempty
  have hA := (Finset.mem_filter.mp hAgood).2
  refine ⟨A, hA.1, ?_, hA.2⟩
  intro g hg ℓ hℓ
  let u : A → I → K := fun i => coordSub q D g ((Pi.basisFun K I) i.val)
  let V := Submodule.span K (Set.range u)
  have htri := coordSub_triangular (K := K) (n := n) (q := q) (D := D) hq g hg
  have hd : ∀ i : A, u i i.val ≠ 0 := fun i => htri.1 i.val
  have hu : ∀ (i : A) j, w j < w i.val → u i j = 0 := fun i j hj => htri.2 i.val j hj
  have hVi : LinearIndependent K u := LinearIndependent.of_comp (coordProj A)
    (upper_projected_independent w hw A u hd hu)
  have hVdim : Module.finrank K V = A.card :=
    (finrank_span_eq_card hVi).trans (Fintype.card_coe A)
  have hVeq : V = (cSpan (K := K) A).map (coordSub q D g) := by
    rw [cSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  have hVr : symbolicRank K n q D (V.map E.toLinearMap) ≤ r := by
    rw [hVeq]
    exact (coordSub_rank_le q hD g hg (cSpan (K := K) A)).trans hA.2
  let B := initialFamily w V
  have hBgood : B ∈ good := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    constructor
    · exact (initialFamily_card w hw V).trans (hVdim.trans hA.1)
    · exact (initial_symbolic_rank_le q hq hD V).trans hVr
  have hweights : (∑ b ∈ B, w b) ≤ ∑ a ∈ A, w a := hmax B hBgood
  have hVA : V = cSpan (K := K) A := upper_initial_span_eq w hw A u hd hu hweights
  obtain ⟨v, hv, rfl⟩ := hℓ
  have hgv : coordSub q D g v ∈ cSpan (K := K) A := by
    rw [← hVA, hVeq]
    exact Submodule.mem_map_of_mem hv
  exact ⟨coordSub q D g v, hgv, dc_coordSub g v⟩


private lemma generic_rank_avoiding {K R J : Type*} [Field K] [Infinite K]
    [Fintype R] [Fintype J] [DecidableEq J] {n : ℕ}
    (M : Matrix R J (MvPolynomial (Fin n) K))
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    ∃ a : Fin n → K, eval a p ≠ 0 ∧
      (M.map (eval a)).rank =
        (M.map (algebraMap _ (FractionRing (MvPolynomial (Fin n) K)))).rank := by
  classical
  let P := MvPolynomial (Fin n) K
  let F := FractionRing P
  let l : P →+* F := algebraMap P F
  obtain ⟨B, hB, hb⟩ := completion (L := K) M l
  have hn : B.det ≠ 0 := by intro h; rw [h, map_zero] at hB; exact hB rfl
  obtain ⟨a, ha⟩ : ∃ a : Fin n → K, eval a (B.det * p) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hn hp (MvPolynomial.funext fun a => by simpa using h a)
  have hap : eval a p ≠ 0 := right_ne_zero_of_mul (by simpa only [map_mul] using ha)
  have hdet : (B.map (eval a)).det ≠ 0 := by
    change ((eval a).mapMatrix B).det ≠ 0
    rw [← RingHom.map_det]
    exact left_ne_zero_of_mul (by simpa only [map_mul] using ha)
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have hh := hb (eval a)
  rw [hrank] at hh
  have hle := (M.map l).rank_le_card_width
  have hspec := rank_specialization M a
  change (M.map (eval a)).rank ≤ (M.map l).rank at hspec
  refine ⟨a, hap, ?_⟩
  change (M.map (eval a)).rank = (M.map l).rank
  omega

private lemma exists_special_rank_first {K : Type*} [Field K] [Infinite K]
    (n q D : ℕ) (hn : 0 < n)
    (W : Submodule K (Module.Dual K (Rd K n q D))) :
    ∃ a : Fin n → K, a ⟨0, hn⟩ ≠ 0 ∧
      Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict W)) =
        symbolicRank K n q D W := by
  letI : Module.Free K W := Module.Free.of_divisionRing K W
  let v : Fin (Module.finrank K W) → Module.Dual K (Rd K n q D) :=
    fun i => ((Module.finBasis K W) i).val
  have hs : Submodule.span K (Set.range v) = W := span_basis_vals W
  obtain ⟨a, ha, hr⟩ := generic_rank_avoiding (genMatrix n q D v)
    (X (⟨0, hn⟩ : Fin n)) (X_ne_zero _)
  rw [genMatrix_eval_rank, genMatrix_rank, hs] at hr
  exact ⟨a, by simpa only [eval_X] using ha, hr⟩

private lemma action_special_rank_eq {K : Type*} [Field K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hD : 2 ≤ D)
    (G : Matrix (Fin n) (Fin n) K) (hG : G.det ≠ 0)
    (W : Submodule K (Module.Dual K (Rd K n q D))) (a : Fin n → K) :
    Module.finrank K (LinearMap.range ((contraction K n q D a).domRestrict
      (W.map (dualAct q D G)))) =
    Module.finrank K (LinearMap.range ((contraction K n q D (G.mulVec a)).domRestrict W)) := by
  have he : (contraction K n q D a).comp (dualAct q D G) =
      (dualAct q (D - 2) G).comp (contraction K n q D (G.mulVec a)) := by
    apply LinearMap.ext
    intro ℓ
    exact contraction_covariance q hD G a ℓ
  have hr : LinearMap.range ((contraction K n q D a).domRestrict (W.map (dualAct q D G))) =
      (LinearMap.range ((contraction K n q D (G.mulVec a)).domRestrict W)).map
        (dualAct q (D - 2) G) := by
    simp only [LinearMap.range_domRestrict, ← Submodule.map_comp]
    rw [he]
  calc
    _ = Module.finrank K ((LinearMap.range ((contraction K n q D (G.mulVec a)).domRestrict W)).map
        (dualAct q (D - 2) G)) := congrArg (fun U : Submodule K (Module.Dual K (Rd K n q (D - 2))) =>
          Module.finrank K U) hr
    _ = _ := (subEquiv q G hG (D - 2)).dualMap.finrank_map_eq _

private lemma first_column_borel {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (a : Fin n → K) (ha : a ⟨0, hn⟩ ≠ 0) :
    ∃ G : Matrix (Fin n) (Fin n) K,
      G.det ≠ 0 ∧ IsBorel (fun j => linForm (cols G j)) ∧
        G.mulVec (Pi.single (⟨0, hn⟩ : Fin n) 1) = a := by
  classical
  let z : Fin n := ⟨0, hn⟩
  let G : Matrix (Fin n) (Fin n) K := fun i j => if j = z then a i else if i = j then 1 else 0
  have htri : G.IsLowerTriangular := by
    intro i j hij
    have hj : j ≠ z := by intro he; subst j; change i.val < 0 at hij; omega
    have hij' : i ≠ j := ne_of_lt hij
    simp [G, hj, hij']
  have hdet : G.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular G htri]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    by_cases hj : j = z
    · subst j; simpa only [G, if_pos rfl] using ha
    · simp [G, hj]
  refine ⟨G, hdet, ?_, ?_⟩
  · intro j
    by_cases hj : j = z
    · subst j
      refine ⟨a z, ha, a, ?_⟩
      have he : cols G z = a := by ext i; simp [cols, G]
      change linForm (cols G z) = _
      rw [he]
      have hf : Finset.univ.filter (fun i : Fin n => z < i) = Finset.univ.erase z := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        simp only [ne_eq, Fin.ext_iff]
        change (0 < i.val) ↔ ¬i.val = 0
        omega
      rw [hf]
      exact (Finset.add_sum_erase Finset.univ (fun i : Fin n => C (a i) * X i)
        (Finset.mem_univ z)).symm
    · refine ⟨1, one_ne_zero, (fun _ => 0), ?_⟩
      have he : cols G j = cols (1 : Matrix (Fin n) (Fin n) K) j := by
        ext i
        simp [cols, G, hj, Matrix.one_apply]
      change linForm (cols G j) = _
      rw [he, linForm_unit]
      simp
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Finset.sum_eq_single z]
    · simp [G, z]
    · intro j _ hj; simp [show j ≠ (⟨0, hn⟩ : Fin n) from hj, hj, Ne.symm hj]
    · simp

private lemma invariant_first_rank {K : Type*} [Field K] [Infinite K] (q : ℕ)
    [Fact q.Prime] [CharP K q] {n D : ℕ} (hn : 0 < n) (hD : 2 ≤ D)
    (W : Submodule K (Module.Dual K (Rd K n q D))) (hW : IsBorelInvariant q D W) :
    Module.finrank K (LinearMap.range ((contraction K n q D
      (Pi.single (⟨0, hn⟩ : Fin n) 1)).domRestrict W)) = symbolicRank K n q D W := by
  classical
  obtain ⟨a, ha, hr⟩ := exists_special_rank_first n q D hn W
  obtain ⟨G, hG, hBG, hGa⟩ := first_column_borel hn a ha
  have hle : W.map (dualAct q D G) ≤ W := by
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact hW _ hBG ℓ hℓ
  have hdim : Module.finrank K (W.map (dualAct q D G)) = Module.finrank K W :=
    (subEquiv q G hG D).dualMap.finrank_map_eq W
  have hWeq : W.map (dualAct q D G) = W := Submodule.eq_of_le_of_finrank_eq hle hdim
  have hh := action_special_rank_eq q hD G hG W (Pi.single (⟨0, hn⟩ : Fin n) 1)
  rw [hWeq, hGa, hr] at hh
  exact hh

end
end BorelProof

namespace ShadowProof
set_option maxHeartbeats 1000000


open BorelProof

@[simp] private lemma mono_apply {n q d : ℕ} (a : ReducedMono n q d) (j : Fin n) :
    a.toFinsupp j = (a.val j : ℕ) := rfl

private lemma erase_decompose {n : ℕ} (a : Fin n →₀ ℕ) (z : Fin n) :
    a.erase z + Finsupp.single z (a z) = a := by
  classical
  ext j
  by_cases hj : j = z <;> simp [hj, Finsupp.erase_apply, Finsupp.single_apply]

private lemma erase_degree {n : ℕ} (a : Fin n →₀ ℕ) (z : Fin n) :
    (a.erase z).degree + a z = a.degree := by
  have h := congrArg Finsupp.degree (erase_decompose a z)
  simpa only [map_add, Finsupp.degree_single] using h

private noncomputable def toReduced {n q d : ℕ} (a : Fin n →₀ ℕ)
    (ha : ∀ j, a j < q) (hd : a.degree = d) : ReducedMono n q d :=
  ⟨fun j => ⟨a j, ha j⟩, by simpa only [← Finsupp.degree_eq_sum] using hd⟩

private lemma toReduced_finsupp {n q d : ℕ} (a : Fin n →₀ ℕ)
    (ha : ∀ j, a j < q) (hd : a.degree = d) :
    (toReduced a ha hd).toFinsupp = a := by ext j; rfl

private noncomputable def dropMono {n q D : ℕ} (a : ReducedMono n q D)
    (z : Fin n) (k : ℕ) (hk : k ≤ (a.val z : ℕ)) : ReducedMono n q (D - k) := by
  classical
  let b := a.toFinsupp - Finsupp.single z k
  have hle : Finsupp.single z k ≤ a.toFinsupp := Finsupp.single_le_iff.mpr hk
  have hb : b + Finsupp.single z k = a.toFinsupp := tsub_add_cancel_of_le hle
  have hd : b.degree + k = D := by
    have h := congrArg Finsupp.degree hb
    simpa only [map_add, Finsupp.degree_single, mono_degree] using h
  exact toReduced b (fun j => (tsub_le_self.trans_lt (a.val j).isLt)) (by omega)

private lemma dropMono_add {n q D : ℕ} (a : ReducedMono n q D) (z : Fin n)
    (k : ℕ) (hk : k ≤ (a.val z : ℕ)) :
    (dropMono a z k hk).toFinsupp + Finsupp.single z k = a.toFinsupp := by
  rw [dropMono, toReduced_finsupp]
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hk)

private noncomputable def shear {K : Type*} [Field K] {n : ℕ}
    (z j : Fin n) : Fin n → MvPolynomial (Fin n) K :=
  fun i => if i = z then X z + X j else X i

private lemma shear_borel {K : Type*} [Field K] {n : ℕ} (z j : Fin n) (hj : z < j) :
    IsBorel (shear (K := K) z j) := by
  classical
  intro i
  by_cases hi : i = z
  · subst i
    refine ⟨1, one_ne_zero, Pi.single j 1, ?_⟩
    simp only [shear, if_pos rfl, map_one, one_mul]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Pi.single_apply, hk, Ne.symm hk]
    · intro hn; exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
  · refine ⟨1, one_ne_zero, (fun _ => 0), ?_⟩
    simp [shear, hi]

private lemma shear_erase {K : Type*} [Field K] {n : ℕ} (z j : Fin n)
    (a : Fin n →₀ ℕ) :
    aeval (R := K) (shear (K := K) z j) (monomial (a.erase z) (1 : K)) =
      monomial (a.erase z) 1 := by
  classical
  rw [aeval_monomial, monomial_eq]
  simp only [map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = z
  · subst i; simp
  · simp [shear, hi]

private lemma shear_monomial {K : Type*} [Field K] {n : ℕ} (z j : Fin n)
    (a : Fin n →₀ ℕ) :
    aeval (R := K) (shear (K := K) z j) (monomial a (1 : K)) =
      (X z + X j) ^ a z * monomial (a.erase z) 1 := by
  have he : monomial a (1 : K) =
      X z ^ a z * monomial (a.erase z) 1 := by
    rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm, erase_decompose]
  rw [he, map_mul, map_pow, aeval_X, shear, if_pos rfl, shear_erase]

private lemma coeff_binomial_one {K : Type*} [Field K] {n : ℕ}
    (z j : Fin n) (hj : j ≠ z) (d : ℕ) :
    coeff (Finsupp.single z d + Finsupp.single j 1)
      ((X z + X j : MvPolynomial (Fin n) K) ^ (d + 1)) = (d + 1 : ℕ) := by
  classical
  rw [add_comm (X z), add_pow, coeff_sum]
  have hterm (k : ℕ) :
      coeff (Finsupp.single z d + Finsupp.single j 1)
        (X j ^ k * X z ^ (d + 1 - k) * ((d + 1).choose k : MvPolynomial (Fin n) K)) =
        if k = 1 then (d + 1 : K) else 0 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    rw [show (((d + 1).choose k : ℕ) : MvPolynomial (Fin n) K) =
      C (((d + 1).choose k : ℕ) : K) by simp]
    rw [mul_comm _ (C _), C_mul_monomial, coeff_monomial]
    by_cases hk : k = 1
    · subst k
      simp [Nat.choose_one_right, add_comm]
    · have he : Finsupp.single j k + Finsupp.single z (d + 1 - k) ≠
          Finsupp.single z d + Finsupp.single j 1 := by
        intro he
        have hh := congrArg (fun a : Fin n →₀ ℕ => a j) he
        exact hk (by simpa [hj, Ne.symm hj] using hh)
      simp only [if_neg hk, if_neg he, if_neg (Ne.symm he)]
  simp_rw [hterm]
  simp


private noncomputable def raiseMono {n q D : ℕ} (a : ReducedMono n q D)
    (z j : Fin n) (hj : j ≠ z) (hp : 0 < (a.val j : ℕ))
    (hz : (a.val z : ℕ) + 1 < q) : ReducedMono n q D := by
  classical
  let b : Fin n →₀ ℕ := a.toFinsupp - Finsupp.single j 1
  have hb : b + Finsupp.single j 1 = a.toFinsupp :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hp)
  have hd : b.degree + 1 = D := by
    have h := congrArg Finsupp.degree hb
    simpa only [map_add, Finsupp.degree_single, mono_degree] using h
  refine toReduced (b + Finsupp.single z 1) ?_ ?_
  · intro i
    by_cases hi : i = z
    · subst i
      simpa [b, Finsupp.single_apply, hj, Ne.symm hj] using hz
    · have hle : (b + Finsupp.single z 1 : Fin n →₀ ℕ) i ≤ (a.val i : ℕ) := by
        simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, add_zero]
        exact tsub_le_self
      exact hle.trans_lt (a.val i).isLt
  · simpa only [map_add, Finsupp.degree_single] using hd

private lemma raiseMono_finsupp {n q D : ℕ} (a : ReducedMono n q D)
    (z j : Fin n) (hj : j ≠ z) (hp : 0 < (a.val j : ℕ))
    (hz : (a.val z : ℕ) + 1 < q) :
    (raiseMono a z j hj hp hz).toFinsupp = a.toFinsupp - Finsupp.single j 1 + Finsupp.single z 1 := by
  rw [raiseMono, toReduced_finsupp]

private lemma raiseMono_at {n q D : ℕ} (a : ReducedMono n q D)
    (z j : Fin n) (hj : j ≠ z) (hp : 0 < (a.val j : ℕ))
    (hz : (a.val z : ℕ) + 1 < q) :
    ((raiseMono a z j hj hp hz).val z : ℕ) = (a.val z : ℕ) + 1 := by
  have h := congrArg (fun f : Fin n →₀ ℕ => f z) (raiseMono_finsupp a z j hj hp hz)
  simpa [hj, Ne.symm hj] using h

private lemma raiseMono_shear_coeff {K : Type*} [Field K] {n q D : ℕ}
    (a : ReducedMono n q D) (z j : Fin n) (hj : j ≠ z)
    (hp : 0 < (a.val j : ℕ)) (hz : (a.val z : ℕ) + 1 < q) :
    coeff a.toFinsupp (aeval (R := K) (shear (K := K) z j)
      (monomial (raiseMono a z j hj hp hz).toFinsupp (1 : K))) = (a.val z : ℕ) + 1 := by
  classical
  let b := raiseMono a z j hj hp hz
  have hindex : (Finsupp.single z (a.val z : ℕ) + Finsupp.single j 1) +
      b.toFinsupp.erase z = a.toFinsupp := by
    rw [show b.toFinsupp = _ from raiseMono_finsupp a z j hj hp hz]
    ext i
    by_cases hi : i = z
    · subst i; simp [Finsupp.erase_apply, Finsupp.single_apply, hj, Ne.symm hj]
    · by_cases hij : i = j
      · subst i
        simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hj, Finsupp.single_eq_same,
          zero_add, Finsupp.erase_ne hj, Finsupp.tsub_apply, add_zero]
        exact Nat.add_sub_of_le hp
      · simp [Finsupp.erase_apply, Finsupp.single_apply, hi, hij]
  rw [shear_monomial]
  have hbz : b.toFinsupp z = (a.val z : ℕ) + 1 := raiseMono_at a z j hj hp hz
  rw [hbz]
  calc
    _ = coeff ((Finsupp.single z (a.val z : ℕ) + Finsupp.single j 1) + b.toFinsupp.erase z)
        ((X z + X j : MvPolynomial (Fin n) K) ^ ((a.val z : ℕ) + 1) * monomial (b.toFinsupp.erase z) 1) :=
      congrArg (fun f : Fin n →₀ ℕ => coeff f _) hindex.symm
    _ = _ := by rw [coeff_mul_monomial, mul_one, coeff_binomial_one z j hj]; norm_cast

private lemma monomial_borel_move {K : Type*} [Field K] (q : ℕ) [Fact q.Prime]
    [CharP K q] {n D : ℕ} (A : Finset (ReducedMono n q D))
    (hA : IsBorelInvariant q D ((cSpan (K := K) A).map
      (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap))
    (a : ReducedMono n q D) (ha : a ∈ A) (z j : Fin n) (hj : z < j)
    (hp : 0 < (a.val j : ℕ)) (hz : (a.val z : ℕ) + 1 < q) :
    raiseMono a z j (ne_of_gt hj) hp hz ∈ A := by
  classical
  let E := dc (K := K) (n := n) (q := q) (d := D)
  let g := shear (K := K) z j
  let v := (Pi.basisFun K (ReducedMono n q D)) a
  have hv : v ∈ cSpan (K := K) A := Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  have himage := hA g (shear_borel z j hj) (E v) ⟨v, hv, rfl⟩
  obtain ⟨u, hu, hue⟩ := himage
  have hcoord : coordSub q D g v ∈ cSpan (K := K) A := by
    have he : coordSub q D g v = u := E.injective ((dc_coordSub g v).trans hue.symm)
    rw [he]
    exact hu
  by_contra hnot
  have hzero := (cSpan_mem A _).mp hcoord _ hnot
  change coordSub q D g ((Pi.basisFun K _) a) (raiseMono a z j (ne_of_gt hj) hp hz) = 0 at hzero
  rw [coordSub_entry, raiseMono_shear_coeff] at hzero
  have hdvd : q ∣ (a.val z : ℕ) + 1 := (CharP.cast_eq_zero_iff K q _).mp (by exact_mod_cast hzero)
  have hh := Nat.eq_zero_of_dvd_of_lt hdvd hz
  omega


private noncomputable def slices {n q D : ℕ} (A : Finset (ReducedMono n q D))
    (z : Fin n) (d : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact (A.filter (fun a => (a.val z : ℕ) = d)).image (fun a => a.toFinsupp.erase z)

private lemma mem_slices {n q D : ℕ} (A : Finset (ReducedMono n q D))
    (z : Fin n) (d : ℕ) (b : Fin n →₀ ℕ) :
    b ∈ slices A z d ↔ ∃ a ∈ A, (a.val z : ℕ) = d ∧ a.toFinsupp.erase z = b := by
  classical
  simp only [slices, Finset.mem_image, Finset.mem_filter, exists_and_left, and_assoc]

private lemma slices_valid {n q D : ℕ} (A : Finset (ReducedMono n q D))
    (z : Fin n) (d : ℕ) (b : Fin n →₀ ℕ) (hb : b ∈ slices A z d) :
    (∀ j, b j < q) ∧ monoDeg b = D - d ∧ b z = 0 := by
  obtain ⟨a, ha, haz, rfl⟩ := (mem_slices A z d b).mp hb
  refine ⟨?_, ?_, Finsupp.erase_same⟩
  · intro j
    by_cases hj : j = z
    · subst j; simp only [Finsupp.erase_same]; exact Nat.zero_lt_of_lt (a.val z).isLt
    · simpa only [Finsupp.erase_ne hj, mono_apply] using (a.val j).isLt
  · have hd := erase_degree a.toFinsupp z
    rw [mono_apply, haz, mono_degree] at hd
    rw [monoDeg, ← Finsupp.degree_eq_sum]
    omega

private lemma slices_card {n q D : ℕ} (A : Finset (ReducedMono n q D))
    (z : Fin n) (d : ℕ) :
    (slices A z d).card = (A.filter (fun a => (a.val z : ℕ) = d)).card := by
  classical
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  apply mono_injective
  change a.toFinsupp.erase z = b.toFinsupp.erase z at he
  have haz := (Finset.mem_filter.mp ha).2
  have hbz := (Finset.mem_filter.mp hb).2
  calc
    a.toFinsupp = a.toFinsupp.erase z + Finsupp.single z d := by
      rw [← haz]; exact (erase_decompose a.toFinsupp z).symm
    _ = b.toFinsupp.erase z + Finsupp.single z d := by rw [he]
    _ = b.toFinsupp := by rw [← hbz]; exact erase_decompose b.toFinsupp z

private lemma exponent_le_min {n q D : ℕ} (a : ReducedMono n q D) (z : Fin n) :
    (a.val z : ℕ) ≤ min (q - 1) D := by
  have hq := (a.val z).isLt
  have hd := Finsupp.le_degree z a.toFinsupp
  rw [mono_apply, mono_degree] at hd
  omega

private lemma slices_sum {n q D : ℕ} (A : Finset (ReducedMono n q D)) (z : Fin n) :
    ∑ d ∈ Finset.range (min (q - 1) D + 1), (slices A z d).card = A.card := by
  classical
  simp_rw [slices_card]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun a : ReducedMono n q D => (a.val z : ℕ))
    (s := A) (t := Finset.range (min (q - 1) D + 1))
    (fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (exponent_le_min a z)))).symm

private lemma slices_high_sum {n q D : ℕ} (A : Finset (ReducedMono n q D)) (z : Fin n) :
    ∑ d ∈ Finset.Icc 2 (min (q - 1) D), (slices A z d).card =
      (A.filter (fun a => 2 ≤ (a.val z : ℕ))).card := by
  classical
  simp_rw [slices_card]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro a ha
  simp only [Finset.mem_Icc, and_iff_left_iff_imp]
  intro _
  exact exponent_le_min a z

private lemma slices_shadow {K : Type*} [Field K] (q : ℕ) [Fact q.Prime] [CharP K q]
    {n D : ℕ} (hn : 0 < n) (A : Finset (ReducedMono n q D))
    (hA : IsBorelInvariant q D ((cSpan (K := K) A).map
      (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap))
    (d : ℕ) (hd : d < min (q - 1) D) :
    shadow (slices A ⟨0, hn⟩ d) ⊆ slices A ⟨0, hn⟩ (d + 1) := by
  classical
  let z : Fin n := ⟨0, hn⟩
  intro b hb
  obtain ⟨a', ha', hb'⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb'
  obtain ⟨a, ha, haz, rfl⟩ := (mem_slices A z d a').mp ha'
  have hjpos : 0 < (a.toFinsupp.erase z) j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
  have hjz : j ≠ z := by intro he; subst j; simp at hjpos
  have haj : 0 < (a.val j : ℕ) := by simpa only [Finsupp.erase_ne hjz, mono_apply] using hjpos
  have hjgt : z < j := by
    change 0 < j.val
    by_contra hh
    apply hjz
    apply Fin.ext
    change j.val = 0
    omega
  have hz : (a.val z : ℕ) + 1 < q := by omega
  let aNew := raiseMono a z j hjz haj hz
  have hnew : aNew ∈ A := monomial_borel_move q A hA a ha z j hjgt haj hz
  apply (mem_slices A z (d + 1) _).mpr
  refine ⟨aNew, hnew, ?_, ?_⟩
  · rw [raiseMono_at, haz]
  · rw [raiseMono_finsupp]
    ext i
    by_cases hi : i = z
    · subst i; simp [Finsupp.erase_apply, Finsupp.single_apply, hjz, Ne.symm hjz]
    · simp [Finsupp.erase_apply, Finsupp.single_apply, hi]


private lemma linForm_single {K : Type*} [Field K] {n : ℕ} (z : Fin n) :
    linForm (Pi.single z (1 : K)) = (X z : MvPolynomial (Fin n) K) := by
  classical
  unfold linForm
  rw [Finset.sum_eq_single z]
  · simp
  · intro i _ hi; simp [Pi.single_apply, hi, Ne.symm hi]
  · simp

private lemma contraction_drop_pairing {K : Type*} [Field K] {n q D : ℕ}
    (a b : ReducedMono n q D) (z : Fin n) (hb : 2 ≤ (b.val z : ℕ)) :
    contraction K n q D (Pi.single z 1)
      (dc (K := K) (n := n) (q := q) (d := D) ((Pi.basisFun K _) a))
      ((Pi.basisFun K (ReducedMono n q (D - 2))) (dropMono b z 2 hb)) =
      if a = b then 1 else 0 := by
  classical
  rw [dc_basis_coeffFunctional]
  change coeff a.toFinsupp (Rd.toPoly K n q D (Rd.ofPoly K n q D
    (linForm (Pi.single z (1 : K)) ^ 2 * Rd.toPoly K n q (D - 2)
      ((Pi.basisFun K _) (dropMono b z 2 hb))))) = _
  rw [toPoly_coeff]
  simp only [Rd.ofPoly, LinearMap.pi_apply, lcoeff_apply]
  rw [linForm_single, Pi.basisFun_apply, toPoly_single, X_pow_eq_monomial,
    monomial_mul, one_mul, add_comm (Finsupp.single z 2), dropMono_add]
  simp only [coeff_monomial, mono_injective.eq_iff, eq_comm]

private lemma contraction_high_card {K : Type*} [Field K] {n q D : ℕ}
    (A : Finset (ReducedMono n q D)) (z : Fin n) :
    (A.filter (fun a => 2 ≤ (a.val z : ℕ))).card ≤
      Module.finrank K (LinearMap.range ((contraction K n q D (Pi.single z 1)).domRestrict
        ((cSpan (K := K) A).map (dc (K := K) (n := n) (q := q) (d := D)).toLinearMap))) := by
  classical
  let B := A.filter (fun a => 2 ≤ (a.val z : ℕ))
  let E := dc (K := K) (n := n) (q := q) (d := D)
  let v : B → Module.Dual K (Rd K n q (D - 2)) := fun a =>
    contraction K n q D (Pi.single z 1) (E ((Pi.basisFun K _) a.val))
  have hind : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    let b := dropMono i.val z 2 (Finset.mem_filter.mp i.property).2
    have he := congrArg (fun f : Module.Dual K (Rd K n q (D - 2)) =>
      f ((Pi.basisFun K _) b)) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul] at he
    have hpair (j : B) : v j ((Pi.basisFun K _) b) = if j = i then 1 else 0 := by
      have hh := contraction_drop_pairing (K := K) j.val i.val z (Finset.mem_filter.mp i.property).2
      simpa only [Subtype.val_inj] using hh
    simp only [hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    exact he
  have hrange : Submodule.span K (Set.range v) ≤
      LinearMap.range ((contraction K n q D (Pi.single z 1)).domRestrict
        ((cSpan (K := K) A).map E.toLinearMap)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨E ((Pi.basisFun K _) i.val), ?_⟩, rfl⟩
    refine ⟨(Pi.basisFun K _) i.val, Submodule.subset_span ?_, rfl⟩
    exact ⟨⟨i.val, (Finset.mem_filter.mp i.property).1⟩, rfl⟩
  have hdim := Submodule.finrank_mono hrange
  have heq := finrank_span_eq_card hind
  rw [heq, Fintype.card_coe] at hdim
  exact hdim

end ShadowProof

theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D)
    (W : Submodule (AlgebraicClosure (ZMod q))
      (Module.Dual (AlgebraicClosure (ZMod q)) (Rd (AlgebraicClosure (ZMod q)) n q D)))
    (hW : W ≠ ⊥) :
    ∃ 𝒜 : ℕ → Finset (Fin n →₀ ℕ),
      (∀ d ≤ min (q - 1) D, ∀ α ∈ 𝒜 d, (∀ j, α j < q) ∧ monoDeg α = D - d) ∧
      Module.finrank (AlgebraicClosure (ZMod q)) W =
        ∑ d ∈ Finset.range (min (q - 1) D + 1), (𝒜 d).card ∧
      ∑ d ∈ Finset.Icc 2 (min (q - 1) D), (𝒜 d).card ≤
        symbolicRank (AlgebraicClosure (ZMod q)) n q D W ∧
      ∀ d < min (q - 1) D, shadow (𝒜 d) ⊆ 𝒜 (d + 1) := by

  classical
  let K := AlgebraicClosure (ZMod q)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    haveI : IsEmpty (ReducedMono 0 q D) := ⟨fun a => by
      have hh := a.property
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hh
      omega⟩
    haveI : Subsingleton (Rd K 0 q D) := inferInstance
    haveI : Subsingleton (Module.Dual K (Rd K 0 q D)) := inferInstance
    exact hW (Subsingleton.elim _ _)
  let E := BorelProof.dc (K := K) (n := n) (q := q) (d := D)
  let V := W.map E.symm.toLinearMap
  have hVW : V.map E.toLinearMap = W := by
    apply Submodule.ext
    intro ℓ
    constructor
    · rintro ⟨v, ⟨η, hη, rfl⟩, rfl⟩
      change E (E.symm η) ∈ W
      rw [E.apply_symm_apply]
      exact hη
    · intro hℓ
      exact ⟨E.symm ℓ, ⟨ℓ, hℓ, rfl⟩, E.apply_symm_apply ℓ⟩
  have hdimV : Module.finrank K V = Module.finrank K W := E.symm.finrank_map_eq W
  obtain ⟨A, hcard, hB, hr⟩ := BorelProof.monomial_borel_replacement q (by omega) hD V
  let z : Fin n := ⟨0, hn⟩
  refine ⟨ShadowProof.slices A z, ?_, ?_, ?_, ?_⟩
  · intro d hd α hα
    have hh := ShadowProof.slices_valid A z d α hα
    exact ⟨hh.1, hh.2.1⟩
  · change Module.finrank K W = _
    exact hdimV.symm.trans (hcard.symm.trans (ShadowProof.slices_sum A z).symm)
  · rw [ShadowProof.slices_high_sum]
    have h1 := ShadowProof.contraction_high_card (K := K) A z
    have h2 := BorelProof.special_rank_le n q D
      ((BorelProof.cSpan (K := K) A).map E.toLinearMap) (Pi.single z 1)
    rw [hVW] at hr
    exact h1.trans (h2.trans hr)
  · intro d hd
    exact ShadowProof.slices_shadow q hn A hB d hd

#print axioms solution
