-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_duplicate_free_pareto_cell_cover_ranked_descent
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T19:44:34.834685+00:00
-- url     : https://prove2.me/submissions/1f5580ac-fc4d-454a-8f39-b3528be45b42

import Definitions.Def_PartialMonitoringGame
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.AffineSubspace
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Intrinsic

set_option autoImplicit false

open scoped BigOperators
open Set Topology

namespace BanditAlgorithm

variable {k d : ℕ} {𝕊 : Type*}

private lemma exists_mem_open_avoiding_finite_affineSubspaces
    {V P ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] [IsTopologicalAddTorsor P]
    [BaireSpace P] [Finite ι]
    (A : ι → AffineSubspace ℝ P) (hproper : ∀ i, A i ≠ ⊤)
    {U : Set P} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, x ∉ A i := by
  have hclosed (i : ι) : IsClosed (A i : Set P) := by
    rw [← AffineSubspace.isClosed_direction_iff]
    exact (A i).direction.closed_of_finiteDimensional
  have hnowhere (i : ι) : IsNowhereDense (A i : Set P) := by
    rw [(hclosed i).isNowhereDense_iff]
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    have hspan := isOpen_interior.affineSpan_eq_top hne
    have hle := affineSpan_mono ℝ
      (show interior (A i : Set P) ⊆ (A i : Set P) from interior_subset)
    have htop : (⊤ : AffineSubspace ℝ P) ≤ A i := calc
      (⊤ : AffineSubspace ℝ P) = affineSpan ℝ (interior (A i : Set P)) := hspan.symm
      _ ≤ affineSpan ℝ (A i : Set P) := hle
      _ = A i := AffineSubspace.affineSpan_coe _
    exact hproper i (top_unique htop)
  have hmeagre : IsMeagre (⋃ i, (A i : Set P)) :=
    isMeagre_iUnion fun i ↦ (hnowhere i).isMeagre
  have hnU := not_isMeagre_of_isOpen hUopen hUne
  have hnot : ¬ U ⊆ ⋃ i, (A i : Set P) := fun hsub ↦ hnU (hmeagre.mono hsub)
  rw [Set.not_subset] at hnot
  obtain ⟨x, hxU, hx⟩ := hnot
  refine ⟨x, hxU, ?_⟩
  intro i hi
  exact hx (Set.mem_iUnion.mpr ⟨i, hi⟩)

private lemma affineDim_stdSimplex_add_one (hd : 0 < d) :
    affineDim (stdSimplex ℝ (Fin d)) + 1 = d := by
  classical
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have heq : (fun i : Fin d ↦ Pi.single i (1 : ℝ)) =
      (Pi.basisFun ℝ (Fin d) : Fin d → Fin d → ℝ) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin d) i).symm
  have hli : LinearIndependent ℝ (fun i : Fin d ↦ Pi.single i (1 : ℝ)) := by
    rw [heq]
    exact (Pi.basisFun ℝ (Fin d)).linearIndependent
  have hai : AffineIndependent ℝ (fun i : Fin d ↦ Pi.single i (1 : ℝ)) :=
    hli.affineIndependent
  have hdim := hai.finrank_vectorSpan_add_one
  unfold affineDim
  rw [← convexHull_rangle_single_eq_stdSimplex ℝ (Fin d),
    affineSpan_convexHull, direction_affineSpan]
  simpa using hdim

private lemma fin_one_loss_eq_of_pareto
    {k : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k 1 𝕊)
    {a b : Fin k} (ha : ParetoOptimalAction G a)
    (hb : ParetoOptimalAction G b) : G.L a 0 = G.L b 0 := by
  obtain ⟨u, hua⟩ := ha.1
  obtain ⟨v, hvb⟩ := hb.1
  have hu0 : u 0 = 1 := by simpa using hua.1.2
  have hv0 : v 0 = 1 := by simpa using hvb.1.2
  have hab := hua.2 b
  have hba := hvb.2 a
  simp only [Fin.sum_univ_one] at hab hba
  rw [hu0] at hab
  rw [hv0] at hba
  nlinarith

private lemma affineSpan_eq_of_subset_of_finrank_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {A B : Set E} (hAB : A ⊆ B) (hAne : A.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ A).direction =
      Module.finrank ℝ (affineSpan ℝ B).direction) :
    affineSpan ℝ A = affineSpan ℝ B := by
  have hle : affineSpan ℝ A ≤ affineSpan ℝ B := affineSpan_mono ℝ hAB
  have hdir : (affineSpan ℝ A).direction = (affineSpan ℝ B).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim
  apply AffineSubspace.ext_of_direction_eq hdir
  obtain ⟨x, hxA⟩ := hAne
  exact ⟨x, subset_affineSpan ℝ _ hxA, subset_affineSpan ℝ _ (hAB hxA)⟩

private lemma equal_loss_rows_of_full_dim_cell_intersection
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    {a b : Fin k} (ha : ParetoOptimalAction G a)
    (hne : (pmCell G a ∩ pmCell G b).Nonempty)
    (hdim : affineDim (pmCell G a ∩ pmCell G b) + 1 = d) :
    ∀ i, G.L a i = G.L b i := by
  classical
  have hIntCell : pmCell G a ∩ pmCell G b ⊆ pmCell G a := inter_subset_left
  have hdimIntCell : Module.finrank ℝ
      (affineSpan ℝ (pmCell G a ∩ pmCell G b)).direction =
      Module.finrank ℝ (affineSpan ℝ (pmCell G a)).direction := by
    have hadim := ha.2
    unfold affineDim at hadim hdim
    omega
  have hspanIntCell : affineSpan ℝ (pmCell G a ∩ pmCell G b) =
      affineSpan ℝ (pmCell G a) :=
    affineSpan_eq_of_subset_of_finrank_eq hIntCell hne hdimIntCell
  have hCellSimplex : pmCell G a ⊆ stdSimplex ℝ (Fin d) := fun _ hx ↦ hx.1
  have hdimCellSimplex : Module.finrank ℝ (affineSpan ℝ (pmCell G a)).direction =
      Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin d))).direction := by
    have hsimplex := affineDim_stdSimplex_add_one (d := d) (by
      have : (pmCell G a).Nonempty := ha.1
      obtain ⟨u, hu⟩ := this
      by_contra hd0
      have : d = 0 := Nat.eq_zero_of_not_pos hd0
      subst d
      simpa [stdSimplex_of_isEmpty_index] using hu.1)
    have hadim := ha.2
    unfold affineDim at hadim hsimplex
    omega
  have hspanCellSimplex : affineSpan ℝ (pmCell G a) =
      affineSpan ℝ (stdSimplex ℝ (Fin d)) :=
    affineSpan_eq_of_subset_of_finrank_eq hCellSimplex ha.1 hdimCellSimplex
  have hspan : affineSpan ℝ (pmCell G a ∩ pmCell G b) =
      affineSpan ℝ (stdSimplex ℝ (Fin d)) := hspanIntCell.trans hspanCellSimplex
  let q : (Fin d → ℝ) → ℝ := fun u ↦ ∑ j, (G.L a j - G.L b j) * u j
  have hqzero_mem (u : Fin d → ℝ) (hu : u ∈ pmCell G a ∩ pmCell G b) : q u = 0 := by
    have hab := hu.1.2 b
    have hba := hu.2.2 a
    have hneg : (∑ j, (G.L b j - G.L a j) * u j) = -q u := by
      dsimp [q]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hneg] at hba
    linarith
  have hqzero_span (u : Fin d → ℝ)
      (hu : u ∈ affineSpan ℝ (pmCell G a ∩ pmCell G b)) : q u = 0 := by
    refine affineSpan_induction (k := ℝ) (p := fun v : Fin d → ℝ ↦ q v = 0)
      hu hqzero_mem ?_
    intro c x y z hx hy hz
    dsimp [q] at ⊢ hx hy hz
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hscaled :
        (∑ j, (G.L a j - G.L b j) * (c * (x j - y j))) =
          c * ((∑ j, (G.L a j - G.L b j) * x j) -
            ∑ j, (G.L a j - G.L b j) * y j) := by
      calc
        (∑ j, (G.L a j - G.L b j) * (c * (x j - y j))) =
            ∑ j, (c * ((G.L a j - G.L b j) * x j) -
              c * ((G.L a j - G.L b j) * y j)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = (∑ j, c * ((G.L a j - G.L b j) * x j)) -
            ∑ j, c * ((G.L a j - G.L b j) * y j) := by
              rw [← Finset.sum_sub_distrib]
        _ = c * ((∑ j, (G.L a j - G.L b j) * x j) -
            ∑ j, (G.L a j - G.L b j) * y j) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum, mul_sub]
    calc
      (∑ j, (G.L a j - G.L b j) * (c * (x j - y j))) +
          ∑ j, (G.L a j - G.L b j) * z j =
          c * ((∑ j, (G.L a j - G.L b j) * x j) -
            ∑ j, (G.L a j - G.L b j) * y j) +
            ∑ j, (G.L a j - G.L b j) * z j := by rw [hscaled]
      _ = 0 := by rw [hx, hy, hz]; ring
  intro i
  have hei : Pi.single i (1 : ℝ) ∈ stdSimplex ℝ (Fin d) := single_mem_stdSimplex ℝ i
  have hbasis : Pi.single i (1 : ℝ) ∈
      affineSpan ℝ (pmCell G a ∩ pmCell G b) := by
    rw [hspan]
    exact subset_affineSpan ℝ _ hei
  have hz := hqzero_span _ hbasis
  change (∑ j, (G.L a j - G.L b j) *
    ((Pi.single i (1 : ℝ) : Fin d → ℝ) j)) = 0 at hz
  rw [Fintype.sum_eq_single i, Pi.single_eq_same, mul_one] at hz
  · exact sub_eq_zero.mp hz
  · intro j hji
    simp [Pi.single_apply, hji]

private lemma affineDim_mono {A B : Set (Fin d → ℝ)} (hAB : A ⊆ B) :
    affineDim A ≤ affineDim B := by
  unfold affineDim
  exact Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hAB))

private def simplexSpan (d : ℕ) : AffineSubspace ℝ (Fin d → ℝ) :=
  affineSpan ℝ (stdSimplex ℝ (Fin d))

private def cellInSpan (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Set (simplexSpan d) :=
  {u | (u : Fin d → ℝ) ∈ pmCell G a}

private noncomputable def simplexSpanNonempty (hd : 0 < d) :
    Nonempty (simplexSpan d) := by
  let u : Fin d → ℝ := fun _ ↦ 1 / d
  have hu : u ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [u]
      positivity
    · simp [u, hd.ne']
  exact ⟨⟨u, subset_affineSpan ℝ _ hu⟩⟩

private lemma convex_pmCell' (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    Convex ℝ (pmCell G a) := by
  intro x hx y hy α β hα hβ hsum
  refine ⟨(convex_stdSimplex ℝ (Fin d)) hx.1 hy.1 hα hβ hsum, ?_⟩
  intro c
  have hxc := hx.2 c
  have hyc := hy.2 c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, (G.L a i - G.L c i) * (α * x i + β * y i)) =
      α * ∑ i, (G.L a i - G.L c i) * x i +
        β * ∑ i, (G.L a i - G.L c i) * y i by
    calc
      _ = ∑ i, (α * ((G.L a i - G.L c i) * x i) +
          β * ((G.L a i - G.L c i) * y i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα hxc)
    (mul_nonpos_of_nonneg_of_nonpos hβ hyc)

private lemma affineSpan_cellInSpan_eq_top_of_pareto
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d) {a : Fin k}
    (ha : ParetoOptimalAction G a) :
    affineSpan ℝ (cellInSpan G a) = ⊤ := by
  classical
  have hCellSimplex : pmCell G a ⊆ stdSimplex ℝ (Fin d) := fun _ hx ↦ hx.1
  have hdimCellSimplex : Module.finrank ℝ (affineSpan ℝ (pmCell G a)).direction =
      Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin d))).direction := by
    have hsimplex := affineDim_stdSimplex_add_one (d := d) hd
    have hadim := ha.2
    unfold affineDim at hadim hsimplex
    omega
  have hspanAmbient : affineSpan ℝ (pmCell G a) = simplexSpan d :=
    affineSpan_eq_of_subset_of_finrank_eq hCellSimplex ha.1 hdimCellSimplex
  have himage : (simplexSpan d).subtype '' cellInSpan G a = pmCell G a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, subset_affineSpan ℝ _ hz.1⟩, hz, rfl⟩
  have hmap := AffineSubspace.map_span (simplexSpan d).subtype (cellInSpan G a)
  rw [himage, hspanAmbient] at hmap
  apply top_unique
  intro x hx
  have hxmap : (x : Fin d → ℝ) ∈
      (affineSpan ℝ (cellInSpan G a)).map (simplexSpan d).subtype := by
    rw [hmap]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hxmap
  have : y = x := Subtype.ext hyx
  simpa [this] using hy

private lemma interior_cellInSpan_nonempty_of_pareto
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d) {a : Fin k}
    (ha : ParetoOptimalAction G a) :
    (interior (cellInSpan G a)).Nonempty := by
  have hi := ha.1.intrinsicInterior (convex_pmCell' G a)
  rw [intrinsicInterior, Set.image_nonempty] at hi
  have hCellSimplex : pmCell G a ⊆ stdSimplex ℝ (Fin d) := fun _ hx ↦ hx.1
  have hdimCellSimplex : Module.finrank ℝ (affineSpan ℝ (pmCell G a)).direction =
      Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin d))).direction := by
    have hsimplex := affineDim_stdSimplex_add_one (d := d) hd
    have hadim := ha.2
    unfold affineDim at hadim hsimplex
    omega
  have hspanAmbient : affineSpan ℝ (pmCell G a) = simplexSpan d :=
    affineSpan_eq_of_subset_of_finrank_eq hCellSimplex ha.1 hdimCellSimplex
  rw [hspanAmbient] at hi
  exact hi

private def badSpanInSimplex [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (lam : Fin d → ℝ)
    (a b : Fin k) : AffineSubspace ℝ (simplexSpan d) :=
  (affineSpan ℝ (insert lam (pmCell G a ∩ pmCell G b))).comap
    (simplexSpan d).subtype

private lemma badSpanInSimplex_ne_top
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd2 : 2 ≤ d)
    {S : Finset (Fin k)}
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    {a b : Fin k} (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b)
    (hneigh : ¬ NeighbouringActions G a b) :
    badSpanInSimplex G lam a b ≠ ⊤ := by
  classical
  let I : Set (Fin d → ℝ) := pmCell G a ∩ pmCell G b
  let A : AffineSubspace ℝ (Fin d → ℝ) := affineSpan ℝ (insert lam I)
  have hAle : A ≤ simplexSpan d := by
    rw [affineSpan_le]
    rintro x (rfl | hx)
    · exact subset_affineSpan ℝ _ hlam
    · exact subset_affineSpan ℝ _ hx.1.1
  intro htop
  have hHA : simplexSpan d ≤ A := by
    intro x hx
    let y : simplexSpan d := ⟨x, hx⟩
    have hy : y ∈ badSpanInSimplex G lam a b := by rw [htop]; trivial
    exact hy
  have hAeq : A = simplexSpan d := le_antisymm hAle hHA
  have hHdim := affineDim_stdSimplex_add_one (d := d) (by omega)
  unfold affineDim at hHdim
  by_cases hI : I.Nonempty
  · have hcodim : affineDim I + 2 < d := by
      have ha := hpareto a haS
      have hb := hpareto b hbS
      have hle : affineDim I ≤ affineDim (pmCell G a) := by
        apply affineDim_mono
        exact inter_subset_left
      have hnotfull : affineDim I + 1 ≠ d := by
        intro hfull
        apply hab
        apply hunique a haS b hbS
        apply equal_loss_rows_of_full_dim_cell_intersection G ha
        · exact hI
        · exact hfull
      have hnotfacet : affineDim I + 2 ≠ d := by
        intro hfacet
        apply hneigh
        exact ⟨ha, hb, hI, hfacet⟩
      have hplusOneLe : affineDim I + 1 ≤ d := calc
        affineDim I + 1 ≤ affineDim (pmCell G a) + 1 := Nat.add_le_add_right hle 1
        _ = d := ha.2
      have hplusOneLt : affineDim I + 1 < d :=
        lt_of_le_of_ne hplusOneLe hnotfull
      have hplusTwoLe : affineDim I + 2 ≤ d := by
        omega
      exact lt_of_le_of_ne hplusTwoLe hnotfacet
    have hins : Module.finrank ℝ A.direction ≤ affineDim I + 1 := by
      unfold affineDim
      dsimp [A]
      rw [direction_affineSpan ℝ, direction_affineSpan ℝ]
      exact finrank_vectorSpan_insert_le_set ℝ I lam
    have hsame : Module.finrank ℝ A.direction =
        Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin d))).direction := by
      rw [hAeq]
      rfl
    omega
  · have hIempty : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hI
    have hAdim : Module.finrank ℝ A.direction = 0 := by
      simp [A, I, hIempty, direction_affineSpan]
    have hsame : Module.finrank ℝ A.direction =
        Module.finrank ℝ (affineSpan ℝ (stdSimplex ℝ (Fin d))).direction := by
      rw [hAeq]
      rfl
    omega

private lemma exists_cell_interior_avoiding_bad_spans
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd2 : 2 ≤ d)
    {S : Finset (Fin k)}
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    {b : Fin k} (hbS : b ∈ S) :
    ∃ u ∈ interior (cellInSpan G b),
      ∀ a ∈ S, ∀ c ∈ S, a ≠ c → ¬ NeighbouringActions G a c →
        u ∉ badSpanInSimplex G lam a c := by
  classical
  have hHclosed : IsClosed (simplexSpan d : Set (Fin d → ℝ)) := by
    rw [← AffineSubspace.isClosed_direction_iff]
    exact (simplexSpan d).direction.closed_of_finiteDimensional
  letI : CompleteSpace (simplexSpan d) := hHclosed.completeSpace_coe
  let A : Fin k × Fin k → AffineSubspace ℝ (simplexSpan d) := fun p ↦
    if hp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧
        ¬ NeighbouringActions G p.1 p.2 then
      badSpanInSimplex G lam p.1 p.2 else ⊥
  have hproper : ∀ p, A p ≠ ⊤ := by
    intro p
    by_cases hp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 ∧
        ¬ NeighbouringActions G p.1 p.2
    · simpa [A, hp] using badSpanInSimplex_ne_top G hd2 hpareto hunique
        lam hlam hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    · simp [A, hp]
  obtain ⟨u, hu, havoid⟩ := exists_mem_open_avoiding_finite_affineSubspaces
    A hproper isOpen_interior
      (interior_cellInSpan_nonempty_of_pareto G (by omega) (hpareto b hbS))
  refine ⟨u, hu, ?_⟩
  intro a haS c hcS hac hneigh hmem
  have hp : a ∈ S ∧ c ∈ S ∧ a ≠ c ∧ ¬ NeighbouringActions G a c :=
    ⟨haS, hcS, hac, hneigh⟩
  have hthis := havoid (a, c)
  have hA : A (a, c) = badSpanInSimplex G lam a c := by simp [A, hp]
  rw [hA] at hthis
  exact hthis hmem

private lemma lineMap_avoids_cell_intersection_of_avoids_badSpan
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    (u : simplexSpan d) {a c : Fin k}
    (hu : u ∉ badSpanInSimplex G lam a c)
    {t : ℝ} (ht : t ≠ 1) :
    AffineMap.lineMap (u : Fin d → ℝ) lam t ∉ pmCell G a ∩ pmCell G c := by
  intro hz
  let A : AffineSubspace ℝ (Fin d → ℝ) :=
    affineSpan ℝ (insert lam (pmCell G a ∩ pmCell G c))
  have hlamA : lam ∈ A := subset_affineSpan ℝ _ (Set.mem_insert _ _)
  have hzA : AffineMap.lineMap (u : Fin d → ℝ) lam t ∈ A :=
    subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hz)
  let q : ℝ := -t / (1 - t)
  have hq : 1 - (1 - q) * (1 - t) = 0 := by
    dsimp [q]
    field_simp
    ring
  have huA : (u : Fin d → ℝ) ∈ A := by
    have hline := AffineMap.lineMap_mem q hzA hlamA
    rw [AffineMap.lineMap_lineMap_left, hq, AffineMap.lineMap_apply_zero] at hline
    exact hline
  exact hu huA

private lemma isClosed_pmCell (G : PartialMonitoringGame k d 𝕊) (a : Fin k) :
    IsClosed (pmCell G a) := by
  rw [show pmCell G a = stdSimplex ℝ (Fin d) ∩ {u : Fin d → ℝ |
      ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * u i ≤ 0} by rfl]
  apply (isClosed_stdSimplex ℝ (Fin d)).inter
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro b
  apply isClosed_le
  · apply continuous_finset_sum
    intro i hi
    exact continuous_const.mul (continuous_apply i)
  · exact continuous_const

private lemma exists_neighbour_strictly_better
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd2 : 2 ≤ d)
    {S : Finset (Fin k)}
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (hcover : ∀ u, u ∈ stdSimplex ℝ (Fin d) →
      ∃ a ∈ S, u ∈ pmCell G a)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d))
    {b : Fin k} (hbS : b ∈ S) (hbnot : lam ∉ pmCell G b) :
    ∃ c ∈ S, NeighbouringActions G b c ∧
      ∑ i, G.L c i * lam i < ∑ i, G.L b i * lam i := by
  classical
  obtain ⟨u, huInt, havoid⟩ := exists_cell_interior_avoiding_bad_spans
    G hd2 hpareto hunique lam hlam hbS
  have huCell : (u : Fin d → ℝ) ∈ pmCell G b := by
    change u ∈ cellInSpan G b
    exact interior_subset huInt
  let z : ℝ → (Fin d → ℝ) := fun t ↦
    AffineMap.lineMap (u : Fin d → ℝ) lam t
  have hzcont : Continuous z := by
    dsimp [z]
    fun_prop
  have hzsimplex {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      z t ∈ stdSimplex ℝ (Fin d) := by
    rw [show z t = (1 - t) • (u : Fin d → ℝ) + t • lam by
      dsimp [z]
      rw [AffineMap.lineMap_apply]
      ext i
      simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring]
    exact (convex_stdSimplex ℝ (Fin d)) huCell.1 hlam
      (sub_nonneg.mpr ht1) ht0 (by ring)
  let T : Set ℝ := Set.Icc 0 1 ∩ z ⁻¹' pmCell G b
  have hTcompact : IsCompact T := isCompact_Icc.inter_right
    ((isClosed_pmCell G b).preimage hzcont)
  have hTne : T.Nonempty := by
    refine ⟨0, ⟨by simp, ?_⟩⟩
    simpa [z] using huCell
  obtain ⟨r, hrT, hrmax⟩ := hTcompact.exists_isMaxOn hTne continuousOn_id
  have hr0 : 0 ≤ r := hrT.1.1
  have hr1 : r ≤ 1 := hrT.1.2
  have hrlt : r < 1 := lt_of_le_of_ne hr1 (by
    intro hr
    apply hbnot
    have := hrT.2
    simpa [z, hr] using this)
  let R : {c : Fin k // c ∈ S} → Set ℝ := fun c ↦
    Set.Ioc r 1 ∩ z ⁻¹' pmCell G c
  have hRcover : Set.Ioc r 1 ⊆ ⋃ c, R c := by
    intro t ht
    obtain ⟨c, hcS, hcz⟩ := hcover (z t) (hzsimplex (hr0.trans ht.1.le) ht.2)
    exact Set.mem_iUnion.mpr ⟨⟨c, hcS⟩, ht, hcz⟩
  have hrcl : r ∈ closure (⋃ c, R c) := by
    apply closure_mono hRcover
    rw [closure_Ioc hrlt.ne]
    exact ⟨le_rfl, hrlt.le⟩
  rw [closure_iUnion_of_finite] at hrcl
  obtain ⟨c, hrc⟩ := Set.mem_iUnion.mp hrcl
  have hRne : (R c).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, closure_empty] at hrc
    exact hrc
  obtain ⟨t, htR⟩ := hRne
  have htgt : r < t := htR.1.1
  have ht1 : t ≤ 1 := htR.1.2
  have ht0 : 0 ≤ t := hr0.trans htgt.le
  have hct : z t ∈ pmCell G c := htR.2
  have hbt : z t ∉ pmCell G b := by
    intro hbt
    have htT : t ∈ T := ⟨⟨ht0, ht1⟩, hbt⟩
    exact (not_le_of_gt htgt) (hrmax htT)
  have hcr : z r ∈ pmCell G c := by
    have hsub : R c ⊆ z ⁻¹' pmCell G c := Set.inter_subset_right
    have hccl := closure_mono hsub hrc
    rw [((isClosed_pmCell G c).preimage hzcont).closure_eq] at hccl
    exact hccl
  have hbr : z r ∈ pmCell G b := hrT.2
  have hcb : (c : Fin k) ≠ b := by
    intro h
    rw [h] at hct
    exact hbt hct
  have hneigh : NeighbouringActions G b c := by
    by_contra hn
    have hforbid := lineMap_avoids_cell_intersection_of_avoids_badSpan
      G lam hlam u (havoid b hbS c c.2 hcb.symm hn) hrlt.ne
    exact hforbid ⟨hbr, hcr⟩
  refine ⟨c, c.2, hneigh, ?_⟩
  have hcrt := hct.2 b
  have hstrict_t : (∑ i, G.L c i * z t i) < ∑ i, G.L b i * z t i := by
    have hle : (∑ i, G.L c i * z t i) ≤ ∑ i, G.L b i * z t i := by
      have heq : (∑ i, (G.L c i - G.L b i) * z t i) =
          (∑ i, G.L c i * z t i) - ∑ i, G.L b i * z t i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [heq] at hcrt
      linarith
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hbt
      refine ⟨hct.1, ?_⟩
      intro a
      have hca := hct.2 a
      have hca' : (∑ i, G.L c i * z t i) ≤ ∑ i, G.L a i * z t i := by
        have heq' : (∑ i, (G.L c i - G.L a i) * z t i) =
            (∑ i, G.L c i * z t i) - ∑ i, G.L a i * z t i := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [heq'] at hca
        linarith
      have heqb : (∑ i, G.L b i * z t i) = ∑ i, G.L c i * z t i := heq.symm
      have hba : (∑ i, (G.L b i - G.L a i) * z t i) =
          (∑ i, G.L b i * z t i) - ∑ i, G.L a i * z t i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hba, heqb]
      linarith)
  have heq_r : (∑ i, G.L c i * z r i) = ∑ i, G.L b i * z r i := by
    have hcb' := hcr.2 b
    have hbc' := hbr.2 c
    have ec : (∑ i, (G.L c i - G.L b i) * z r i) =
        (∑ i, G.L c i * z r i) - ∑ i, G.L b i * z r i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have eb : (∑ i, (G.L b i - G.L c i) * z r i) =
        (∑ i, G.L b i * z r i) - ∑ i, G.L c i * z r i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [ec] at hcb'
    rw [eb] at hbc'
    linarith
  have hline (s : ℝ) (a : Fin k) :
      (∑ i, G.L a i * z s i) =
        (1 - s) * (∑ i, G.L a i * (u : Fin d → ℝ) i) +
          s * ∑ i, G.L a i * lam i := by
    have hzform : z s = (1 - s) • (u : Fin d → ℝ) + s • lam := by
      dsimp [z]
      rw [AffineMap.lineMap_apply]
      ext i
      simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hzform]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · calc
        (∑ i, G.L a i * ((1 - s) * (u : Fin d → ℝ) i)) =
            ∑ i, (1 - s) * (G.L a i * (u : Fin d → ℝ) i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (1 - s) * ∑ i, G.L a i * (u : Fin d → ℝ) i := by
          rw [Finset.mul_sum]
    · calc
        (∑ i, G.L a i * (s * lam i)) =
            ∑ i, s * (G.L a i * lam i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = s * ∑ i, G.L a i * lam i := by
          rw [Finset.mul_sum]
  rw [hline t c, hline t b] at hstrict_t
  rw [hline r c, hline r b] at heq_r
  nlinarith

private lemma sum_eq_one_of_mem_simplexSpan (u : simplexSpan d) :
    ∑ i, (u : Fin d → ℝ) i = 1 := by
  refine affineSpan_induction (k := ℝ)
    (p := fun v : Fin d → ℝ ↦ ∑ i, v i = 1)
    u.2 (fun x hx ↦ hx.2) ?_
  intro c x y z hx hy hz
  simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  calc
    (∑ i, c * (x i - y i)) + ∑ i, z i =
        c * ((∑ i, x i) - ∑ i, y i) + ∑ i, z i := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 1 := by rw [hx, hy, hz]; ring

private def lossDiffLinear (G : PartialMonitoringGame k d 𝕊) (a b : Fin k) :
    (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ i, (G.L a i - G.L b i) * u i
  map_add' x y := by
    simp only [Pi.add_apply]
    simp_rw [mul_add]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      (∑ i, (G.L a i - G.L b i) * (c * x i)) =
          ∑ i, c * ((G.L a i - G.L b i) * x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = c * ∑ i, (G.L a i - G.L b i) * x i := by rw [Finset.mul_sum]

private def tieSubspaceInSimplex [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k) :
    AffineSubspace ℝ (simplexSpan d) :=
  (lossDiffLinear G a b).ker.toAffineSubspace.comap (simplexSpan d).subtype

private lemma tieSubspaceInSimplex_ne_top
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) {S : Finset (Fin k)}
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    {a b : Fin k} (haS : a ∈ S) (hbS : b ∈ S) (hab : a ≠ b) :
    tieSubspaceInSimplex G a b ≠ ⊤ := by
  classical
  intro htop
  have hzero (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
      lossDiffLinear G a b u = 0 := by
    let us : simplexSpan d := ⟨u, subset_affineSpan ℝ _ hu⟩
    have hus : us ∈ tieSubspaceInSimplex G a b := by rw [htop]; trivial
    exact hus
  apply hab
  apply hunique a haS b hbS
  intro i
  have hei := single_mem_stdSimplex ℝ i
  have hz := hzero (Pi.single i (1 : ℝ)) hei
  change (∑ j, (G.L a j - G.L b j) *
    ((Pi.single i (1 : ℝ) : Fin d → ℝ) j)) = 0 at hz
  rw [Fintype.sum_eq_single i, Pi.single_eq_same, mul_one] at hz
  · exact sub_eq_zero.mp hz
  · intro j hji
    simp [hji]

private lemma exists_simplex_point_pairwise_loss_distinct
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d)
    {S : Finset (Fin k)}
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b) :
    ∃ g, g ∈ stdSimplex ℝ (Fin d) ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        (∑ i, G.L a i * g i) ≠ ∑ i, G.L b i * g i := by
  classical
  have hHclosed : IsClosed (simplexSpan d : Set (Fin d → ℝ)) := by
    rw [← AffineSubspace.isClosed_direction_iff]
    exact (simplexSpan d).direction.closed_of_finiteDimensional
  letI : CompleteSpace (simplexSpan d) := hHclosed.completeSpace_coe
  let A : Fin k × Fin k → AffineSubspace ℝ (simplexSpan d) := fun p ↦
    if hp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2 then
      tieSubspaceInSimplex G p.1 p.2 else ⊥
  have hproper : ∀ p, A p ≠ ⊤ := by
    intro p
    by_cases hp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2
    · simpa [A, hp] using tieSubspaceInSimplex_ne_top G hunique
        hp.1 hp.2.1 hp.2.2
    · simp [A, hp]
  let g₀ : Fin d → ℝ := fun _ ↦ 1 / d
  have hg₀ : g₀ ∈ stdSimplex ℝ (Fin d) := by
    constructor
    · intro i
      dsimp [g₀]
      positivity
    · simp [g₀, hd.ne']
  let gs₀ : simplexSpan d := ⟨g₀, subset_affineSpan ℝ _ hg₀⟩
  let U : Set (simplexSpan d) := {u | ∀ i, 0 < (u : Fin d → ℝ) i}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ i, {u : simplexSpan d | 0 < (u : Fin d → ℝ) i} by
      ext u; simp [U]]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val)
  have hUne : U.Nonempty := by
    refine ⟨gs₀, ?_⟩
    intro i
    dsimp [gs₀, g₀]
    positivity
  obtain ⟨gs, hgsU, havoid⟩ :=
    exists_mem_open_avoiding_finite_affineSubspaces A hproper hUopen hUne
  let g : Fin d → ℝ := gs
  have hg : g ∈ stdSimplex ℝ (Fin d) := by
    refine ⟨fun i ↦ (hgsU i).le, ?_⟩
    exact sum_eq_one_of_mem_simplexSpan gs
  refine ⟨g, hg, ?_⟩
  intro a haS b hbS hab heq
  have hp : a ∈ S ∧ b ∈ S ∧ a ≠ b := ⟨haS, hbS, hab⟩
  have hnot := havoid (a, b)
  have hA : A (a, b) = tieSubspaceInSimplex G a b := by simp [A, hp]
  rw [hA] at hnot
  apply hnot
  change lossDiffLinear G a b g = 0
  dsimp [lossDiffLinear, g]
  have : (∑ i, G.L a i * g i) - ∑ i, G.L b i * g i = 0 := sub_eq_zero.mpr heq
  rw [← Finset.sum_sub_distrib] at this
  convert this using 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private lemma exists_order_refining_tie_break_perturbation
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d)
    {S : Finset (Fin k)}
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (lam : Fin d → ℝ) (hlam : lam ∈ stdSimplex ℝ (Fin d)) :
    ∃ mu, mu ∈ stdSimplex ℝ (Fin d) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
        (∑ i, G.L a i * mu i) ≠ ∑ i, G.L b i * mu i) ∧
      ∀ a ∈ S, ∀ b ∈ S,
        (∑ i, G.L a i * mu i) < ∑ i, G.L b i * mu i →
          (∑ i, G.L a i * lam i) ≤ ∑ i, G.L b i * lam i := by
  classical
  obtain ⟨g, hg, hgdistinct⟩ :=
    exists_simplex_point_pairwise_loss_distinct G hd hunique
  let val : (Fin d → ℝ) → Fin k → ℝ := fun x a ↦ ∑ i, G.L a i * x i
  let mu : ℝ → Fin d → ℝ := fun e i ↦ (1 - e) * lam i + e * g i
  have hmuval (e : ℝ) (a : Fin k) :
      val (mu e) a = (1 - e) * val lam a + e * val g a := by
    dsimp [val, mu]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · calc
        (∑ i, G.L a i * ((1 - e) * lam i)) =
            ∑ i, (1 - e) * (G.L a i * lam i) := by
              apply Finset.sum_congr rfl; intro i hi; ring
        _ = _ := by rw [Finset.mul_sum]
    · calc
        (∑ i, G.L a i * (e * g i)) =
            ∑ i, e * (G.L a i * g i) := by
              apply Finset.sum_congr rfl; intro i hi; ring
        _ = _ := by rw [Finset.mul_sum]
  have hev (a b : Fin k) : ∀ᶠ e in nhds (0 : ℝ),
      val lam b < val lam a → val (mu e) b < val (mu e) a := by
    by_cases h : val lam b < val lam a
    · have hcont : ContinuousAt (fun e : ℝ ↦ val (mu e) b - val (mu e) a) 0 := by
        simp only [hmuval]
        fun_prop
      have hzero : (fun e : ℝ ↦ val (mu e) b - val (mu e) a) 0 =
          val lam b - val lam a := by simp [hmuval]
      have hneg : val lam b - val lam a < 0 := sub_neg.mpr h
      have hc : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0 := continuousAt_const
      have he := hcont.eventually_lt hc (show val (mu 0) b - val (mu 0) a < 0 by
        calc
          val (mu 0) b - val (mu 0) a = val lam b - val lam a := hzero
          _ < 0 := hneg)
      filter_upwards [he] with e he
      intro _
      exact sub_neg.mp he
    · exact Filter.Eventually.of_forall fun e he ↦ False.elim (h he)
  have hall : ∀ᶠ e in nhds (0 : ℝ), ∀ a b : Fin k,
      val lam b < val lam a → val (mu e) b < val (mu e) a :=
    Filter.eventually_all.mpr fun a ↦ Filter.eventually_all.mpr fun b ↦ hev a b
  have hall' : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ a b : Fin k,
      val lam b < val lam a → val (mu e) b < val (mu e) a :=
    hall.filter_mono inf_le_left
  have hlt1 : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), e < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hpos : ∀ᶠ e in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < e := self_mem_nhdsWithin
  haveI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  obtain ⟨e, hstable, he1, he0⟩ := Filter.Eventually.exists
    (hall'.and (hlt1.and hpos))
  have he0' : 0 ≤ e := he0.le
  have he1' : e ≤ 1 := he1.le
  have hmu : mu e ∈ stdSimplex ℝ (Fin d) := by
    rw [show mu e = (1 - e) • lam + e • g by
      ext i
      simp [mu]]
    exact (convex_stdSimplex ℝ (Fin d)) hlam hg
      (sub_nonneg.mpr he1') he0' (by ring)
  refine ⟨mu e, hmu, ?_, ?_⟩
  · intro a haS b hbS hab heq
    change val (mu e) a = val (mu e) b at heq
    have hgne := hgdistinct a haS b hbS hab
    by_cases hl : val lam a = val lam b
    · have hmudiff : val (mu e) a - val (mu e) b =
          e * (val g a - val g b) := by rw [hmuval, hmuval, hl]; ring
      have : val (mu e) a - val (mu e) b ≠ 0 := by
        rw [hmudiff]
        exact mul_ne_zero he0.ne' (sub_ne_zero.mpr hgne)
      exact this (sub_eq_zero.mpr heq)
    · rcases lt_or_gt_of_ne hl with hlt | hgt
      · exact (ne_of_lt (hstable b a hlt)) heq
      · exact (ne_of_lt (hstable a b hgt)) heq.symm
  · intro a haS b hbS hm
    by_contra hnle
    have hrev : val lam b < val lam a := lt_of_not_ge hnle
    exact (not_lt_of_ge hm.le) (hstable a b hrev)

private lemma ranked_descent_ge_two
    [Nonempty (simplexSpan d)]
    (G : PartialMonitoringGame k d 𝕊) (hd2 : 2 ≤ d)
    (S : Finset (Fin k)) (hSne : S.Nonempty)
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (hcover : ∀ u, u ∈ stdSimplex ℝ (Fin d) →
      ∃ a ∈ S, u ∈ pmCell G a) :
    ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ root ∈ S, ∃ rank : Fin k → ℕ,
        ∀ b ∈ S, b ≠ root →
          ∃ c ∈ S, NeighbouringActions G b c ∧
            ∑ i : Fin d, G.L c i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i ∧
            rank c < rank b := by
  classical
  intro lam hlam
  obtain ⟨mu, hmu, hdistinct, hrefine⟩ :=
    exists_order_refining_tie_break_perturbation G (by omega) hunique lam hlam
  let val : Fin k → ℝ := fun a ↦ ∑ i, G.L a i * mu i
  let vals : Finset ℝ := S.image val
  have hvals : vals.Nonempty := hSne.image val
  let v := vals.min' hvals
  obtain ⟨root, hrootS, hrootv⟩ := Finset.mem_image.mp (vals.min'_mem hvals)
  have hrootle {b : Fin k} (hbS : b ∈ S) : val root ≤ val b := by
    have hbval : val b ∈ vals := Finset.mem_image.mpr ⟨b, hbS, rfl⟩
    have := vals.min'_le _ hbval
    simpa [v, hrootv] using this
  have hrootlt {b : Fin k} (hbS : b ∈ S) (hbr : b ≠ root) :
      val root < val b := by
    exact (hrootle hbS).lt_of_ne (by
      intro heq
      apply hbr
      apply hunique b hbS root hrootS
      by_contra hrows
      apply hdistinct b hbS root hrootS hbr
      exact heq.symm)
  let rank : Fin k → ℕ := fun a ↦ (S.filter fun x ↦ val x < val a).card
  refine ⟨root, hrootS, rank, ?_⟩
  intro b hbS hbr
  have hbnot : mu ∉ pmCell G b := by
    intro hbcell
    have hbro := hbcell.2 root
    have heq : (∑ i, (G.L b i - G.L root i) * mu i) = val b - val root := by
      dsimp [val]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hbro
    linarith [hrootlt hbS hbr]
  obtain ⟨c, hcS, hneigh, hcbmu⟩ := exists_neighbour_strictly_better
    G hd2 hpareto hunique hcover mu hmu hbS hbnot
  have hcblam := hrefine c hcS b hbS hcbmu
  refine ⟨c, hcS, hneigh, hcblam, ?_⟩
  dsimp [rank]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx'.1, lt_trans hx'.2 hcbmu⟩
  · intro heq
    have hcin : c ∈ S.filter fun x ↦ val x < val b :=
      Finset.mem_filter.mpr ⟨hcS, hcbmu⟩
    have hcnin : c ∉ S.filter fun x ↦ val x < val c := by simp
    rw [← heq] at hcin
    exact hcnin hcin

theorem duplicate_free_pareto_cell_cover_ranked_descent
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (hd : 0 < d)
    (S : Finset (Fin k)) (hSne : S.Nonempty)
    (hpareto : ∀ a ∈ S, ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (hcover : ∀ u, u ∈ stdSimplex ℝ (Fin d) →
      ∃ a ∈ S, u ∈ pmCell G a) :
    ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ root ∈ S, ∃ rank : Fin k → ℕ,
        ∀ b ∈ S, b ≠ root →
          ∃ c ∈ S, NeighbouringActions G b c ∧
            ∑ i : Fin d, G.L c i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i ∧
            rank c < rank b := by
  classical
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hd.ne') with hd1 | hd2
  · have hdEq : d = 1 := hd1.symm
    subst d
    let root := hSne.choose
    have hrootS : root ∈ S := hSne.choose_spec
    have hsingleton : ∀ b ∈ S, b = root := by
      intro b hbS
      apply hunique b hbS root hrootS
      intro i
      fin_cases i
      exact fin_one_loss_eq_of_pareto G (hpareto b hbS) (hpareto root hrootS)
    intro lam hlam
    refine ⟨root, hrootS, fun _ ↦ 0, ?_⟩
    intro b hbS hbr
    exact False.elim (hbr (hsingleton b hbS))
  · letI : Nonempty (simplexSpan d) := simplexSpanNonempty (d := d) hd
    exact ranked_descent_ge_two G hd2 S hSne hpareto hunique hcover

end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (hd : 0 < d)
    (S : Finset (Fin k)) (hSne : S.Nonempty)
    (hpareto : ∀ a ∈ S, BanditAlgorithm.ParetoOptimalAction G a)
    (hunique : ∀ a ∈ S, ∀ b ∈ S,
      (∀ i, G.L a i = G.L b i) → a = b)
    (hcover : ∀ u, u ∈ stdSimplex ℝ (Fin d) →
      ∃ a ∈ S, u ∈ BanditAlgorithm.pmCell G a) :
    ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ root ∈ S, ∃ rank : Fin k → ℕ,
        ∀ b ∈ S, b ≠ root →
          ∃ c ∈ S, BanditAlgorithm.NeighbouringActions G b c ∧
            ∑ i : Fin d, G.L c i * lam i ≤
              ∑ i : Fin d, G.L b i * lam i ∧
            rank c < rank b :=
  BanditAlgorithm.duplicate_free_pareto_cell_cover_ranked_descent
    G hd S hSne hpareto hunique hcover
