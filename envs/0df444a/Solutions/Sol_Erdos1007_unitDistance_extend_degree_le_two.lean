-- Prove2me | solution 1 for Erdos1007.unitDistance_extend_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:44.965949+00:00
-- url     : https://prove2.me/submissions/80052959-f303-4821-af9a-a732d660b7b9

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Erdos1007_Geometry_Reattach
section
namespace Erdos1007
open SimpleGraph Metric
open scoped RealInnerProductSpace
private lemma norm_sq_orthonormal {e₀ e₁ : EuclideanSpace ℝ (Fin 3)} (he₀ : ‖e₀‖ = 1)
    (he₁ : ‖e₁‖ = 1) (horth : ⟪e₀, e₁⟫ = 0) (t s : ℝ) :
    ‖t • e₀ + s • e₁‖ ^ 2 = t ^ 2 + s ^ 2 := by
  have hcross : ⟪t • e₀, s • e₁⟫ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, horth]
  rw [norm_add_sq_real, hcross, mul_zero, add_zero, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, he₀, he₁, mul_one, mul_one, sq_abs, sq_abs]
private lemma inner_coord_orthonormal {e₀ e₁ : EuclideanSpace ℝ (Fin 3)} (he₀ : ‖e₀‖ = 1)
    (horth : ⟪e₀, e₁⟫ = 0) (t s : ℝ) : ⟪t • e₀ + s • e₁, e₀⟫ = t := by
  have h10 : ⟪e₁, e₀⟫ = 0 := inner_eq_zero_symm.mp horth
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h10, real_inner_self_eq_norm_sq,
    he₀]
  ring
private lemma norm_eq_of_norm_sq_eq {x : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : 0 ≤ r)
    (hx : ‖x‖ ^ 2 = r ^ 2) : ‖x‖ = r :=
  (sq_eq_sq₀ (norm_nonneg _) hr).mp hx
private lemma infinite_semicircle (c e₀ e₁ : EuclideanSpace ℝ (Fin 3)) (he₀ : ‖e₀‖ = 1)
    (horth : ⟪e₀, e₁⟫ = 0) {r : ℝ} (hr : 0 < r) :
    ((fun t : ℝ => c + t • e₀ + Real.sqrt (r ^ 2 - t ^ 2) • e₁) '' Set.Icc 0 r).Infinite := by
  refine (Set.infinite_image_iff ?_).2 (Set.Icc_infinite hr)
  intro t _ t' _ h
  have hcoord :
      ∀ u : ℝ, ⟪c + u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ - c, e₀⟫ = u := by
    intro u
    have hshift : c + u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ - c =
        u • e₀ + Real.sqrt (r ^ 2 - u ^ 2) • e₁ := by
      abel
    rw [hshift]
    exact inner_coord_orthonormal he₀ horth _ _
  have hinner := congrArg (fun p => ⟪p - c, e₀⟫) h
  rw [hcoord, hcoord] at hinner
  exact hinner
private lemma exists_orthonormal_pair_orthogonal {d : EuclideanSpace ℝ (Fin 3)} (hd : d ≠ 0) :
    ∃ e₀ e₁ : EuclideanSpace ℝ (Fin 3), ‖e₀‖ = 1 ∧ ‖e₁‖ = 1 ∧ ⟪e₀, e₁⟫ = 0 ∧
      ⟪d, e₀⟫ = 0 ∧ ⟪d, e₁⟫ = 0 := by
  let b := @OrthonormalBasis.fromOrthogonalSpanSingleton ℝ _ (EuclideanSpace ℝ (Fin 3)) _ _
    2 ⟨finrank_euclideanSpace_fin⟩ d hd
  refine ⟨b 0, b 1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Submodule.norm_coe (b 0)).trans (b.norm_eq_one 0)
  · exact (Submodule.norm_coe (b 1)).trans (b.norm_eq_one 1)
  · rw [← Submodule.coe_inner]
    exact b.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 1).property
private lemma infinite_unitSphere (c : EuclideanSpace ℝ (Fin 3)) : (sphere c 1).Infinite := by
  let e₀ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  let e₁ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1
  have hort := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)
  have he₀ : ‖e₀‖ = 1 := hort.norm_eq_one 0
  have he₁ : ‖e₁‖ = 1 := hort.norm_eq_one 1
  have horth : ⟪e₀, e₁⟫ = 0 := hort.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)
  refine Set.Infinite.mono ?_ (infinite_semicircle c e₀ e₁ he₀ horth one_pos)
  rintro _ ⟨t, ht, rfl⟩
  have hshift : c + t • e₀ + Real.sqrt ((1 : ℝ) ^ 2 - t ^ 2) • e₁ - c =
      t • e₀ + Real.sqrt ((1 : ℝ) ^ 2 - t ^ 2) • e₁ := by
    abel
  rw [mem_sphere, dist_eq_norm, hshift]
  apply norm_eq_of_norm_sq_eq zero_le_one
  have hs : 0 ≤ (1 : ℝ) ^ 2 - t ^ 2 :=
    sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1]) ht.2
  rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs, one_pow]
  ring
private lemma infinite_unitSphere_inter {c₁ c₂ : EuclideanSpace ℝ (Fin 3)}
    (hdist : dist c₁ c₂ = 1) : (sphere c₁ 1 ∩ sphere c₂ 1).Infinite := by
  let d := c₂ - c₁
  have hd : d ≠ 0 := by
    intro h
    have hc : c₂ = c₁ := eq_of_sub_eq_zero h
    simp [hc, dist_self] at hdist
  have hnorm : ‖d‖ = 1 := by
    rw [← hdist, dist_comm, dist_eq_norm]
  obtain ⟨e₀, e₁, he₀, he₁, horth, hd₀, hd₁⟩ := exists_orthonormal_pair_orthogonal hd
  let r : ℝ := Real.sqrt 3 / 2
  have hr : 0 < r := by positivity
  have hr2 : r ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hhalfScalar : (⅟2 : ℝ) = 1 / 2 := by rw [invOf_eq_inv, inv_eq_one_div]
  let m := midpoint ℝ c₁ c₂
  have hleft : m - c₁ = (1 / 2 : ℝ) • d := by
    unfold m d
    rw [← vsub_eq_sub, midpoint_vsub_left, hhalfScalar, vsub_eq_sub]
  have hright : m - c₂ = -((1 / 2 : ℝ) • d) := by
    unfold m d
    rw [← vsub_eq_sub, midpoint_vsub_right, hhalfScalar, vsub_eq_sub, ← neg_sub c₂ c₁,
      smul_neg]
  let φ : ℝ → EuclideanSpace ℝ (Fin 3) := fun t =>
    m + t • e₀ + Real.sqrt (r ^ 2 - t ^ 2) • e₁
  refine Set.Infinite.mono ?_ (infinite_semicircle m e₀ e₁ he₀ horth hr)
  rintro _ ⟨t, ht, rfl⟩
  have hs : 0 ≤ r ^ 2 - t ^ 2 :=
    sub_nonneg.mpr <| sq_le_sq' (by linarith [ht.1, hr.le]) ht.2
  set s : ℝ := Real.sqrt (r ^ 2 - t ^ 2)
  have hplan : ‖t • e₀ + s • e₁‖ ^ 2 = 3 / 4 := by
    rw [norm_sq_orthonormal he₀ he₁ horth, Real.sq_sqrt hs, hr2]
    ring
  have hcross : ⟪(1 / 2 : ℝ) • d, t • e₀ + s • e₁⟫ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, inner_add_right, hd₀, hd₁]
  have hhalf : ‖(1 / 2 : ℝ) • d‖ ^ 2 = 1 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, hnorm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_one]
    norm_num
  have hφ₁ : φ t - c₁ = (1 / 2 : ℝ) • d + (t • e₀ + s • e₁) := by
    have : φ t - c₁ = (m - c₁) + (t • e₀ + s • e₁) := by
      simp only [φ, s]
      abel
    rw [this, hleft]
  have hφ₂ : φ t - c₂ = -((1 / 2 : ℝ) • d) + (t • e₀ + s • e₁) := by
    have : φ t - c₂ = (m - c₂) + (t • e₀ + s • e₁) := by
      simp only [φ, s]
      abel
    rw [this, hright]
  refine ⟨?_, ?_⟩
  · rw [mem_sphere, dist_eq_norm, hφ₁]
    apply norm_eq_of_norm_sq_eq zero_le_one
    rw [norm_add_sq_real, hcross, mul_zero, add_zero, hhalf, hplan]
    norm_num
  · have hcross' : ⟪-((1 / 2 : ℝ) • d), t • e₀ + s • e₁⟫ = 0 := by
      rw [inner_neg_left, hcross, neg_zero]
    rw [mem_sphere, dist_eq_norm, hφ₂]
    apply norm_eq_of_norm_sq_eq zero_le_one
    rw [norm_add_sq_real, hcross', mul_zero, add_zero, norm_neg, hhalf, hplan]
    norm_num
private lemma extend_unitDistance {V : Type*} {G : SimpleGraph V} {u : V}
    (f : {v : V // v ≠ u} → EuclideanSpace ℝ (Fin 3)) (hfInj : Function.Injective f)
    (hfDist : ∀ a b : {v : V // v ≠ u},
      (G.induce {v | v ≠ u}).Adj a b → dist (f a) (f b) = 1)
    (p : EuclideanSpace ℝ (Fin 3)) (hpOut : p ∉ Set.range f)
    (hpNbr : ∀ ⦃v : V⦄ (hv : G.Adj u v), dist p (f ⟨v, hv.ne'⟩) = 1) :
    ∃ g : V → EuclideanSpace ℝ (Fin 3), Function.Injective g ∧
      ∀ a b, G.Adj a b → dist (g a) (g b) = 1 := by
  classical
  let g : V → EuclideanSpace ℝ (Fin 3) := fun x => if hx : x = u then p else f ⟨x, hx⟩
  refine ⟨g, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · exact ha.trans hb.symm
    · have hga : g a = p := dif_pos ha
      have hgb : g b = f ⟨b, hb⟩ := dif_neg hb
      exact (hpOut ⟨⟨b, hb⟩, hgb.symm.trans (hab.symm.trans hga)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dif_neg ha
      have hgb : g b = p := dif_pos hb
      exact (hpOut ⟨⟨a, ha⟩, hga.symm.trans (hab.trans hgb)⟩).elim
    · have hga : g a = f ⟨a, ha⟩ := dif_neg ha
      have hgb : g b = f ⟨b, hb⟩ := dif_neg hb
      exact congrArg Subtype.val <| hfInj <| hga.symm.trans (hab.trans hgb)
  · intro a b hab
    by_cases ha : a = u <;> by_cases hb : b = u
    · exact (hab.ne (ha.trans hb.symm)).elim
    · have hbu : G.Adj u b := by simpa [ha] using hab
      rw [show g a = p from dif_pos ha, show g b = f ⟨b, hb⟩ from dif_neg hb]
      exact hpNbr hbu
    · have hau : G.Adj u a := by simpa [hb] using hab.symm
      rw [show g a = f ⟨a, ha⟩ from dif_neg ha, show g b = p from dif_pos hb, dist_comm]
      exact hpNbr hau
    · rw [show g a = f ⟨a, ha⟩ from dif_neg ha, show g b = f ⟨b, hb⟩ from dif_neg hb]
      exact hfDist ⟨a, ha⟩ ⟨b, hb⟩ hab
@[expose] public section
end
end Erdos1007
end

set_option autoImplicit false
@[expose] public section
open Erdos1007
open SimpleGraph Metric
open scoped RealInnerProductSpace
public section
namespace Erdos1007
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u : V} (hdeg : G.degree u ≤ 2) :
    (∃ f : {v : V // v ≠ u} → EuclideanSpace ℝ (Fin 3),
        Function.Injective f ∧
        ∀ a b : {v : V // v ≠ u},
          ((G.induce {v | v ≠ u}).Adj a b ∨
            (G.degree u = 2 ∧ a.1 ∈ G.neighborSet u ∧ b.1 ∈ G.neighborSet u ∧ a ≠ b)) →
          dist (f a) (f b) = 1) →
      ∃ g : V → EuclideanSpace ℝ (Fin 3), Function.Injective g ∧
        ∀ a b, G.Adj a b → dist (g a) (g b) = 1 := by
  classical
  rintro ⟨f, hfInj, hfDist⟩
  have hfDist' : ∀ a b : {v : V // v ≠ u},
      (G.induce {v | v ≠ u}).Adj a b → dist (f a) (f b) = 1 :=
    fun a b h => hfDist a b (Or.inl h)
  have hfin : (Set.range f).Finite := Set.finite_range f
  obtain hdeg | hdeg | hdeg : G.degree u = 0 ∨ G.degree u = 1 ∨ G.degree u = 2 := by omega
  · obtain ⟨p, hpOut⟩ := hfin.exists_notMem
    exact extend_unitDistance f hfInj hfDist' p hpOut fun v hv =>
      ((G.degree_eq_zero u).mp hdeg v hv).elim
  · obtain ⟨v, hvAdj, hvUnique⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hdeg
    obtain ⟨p, hpSphere, hpOut⟩ :=
      (infinite_unitSphere (f ⟨v, hvAdj.ne'⟩)).exists_notMem_finite hfin
    refine extend_unitDistance f hfInj hfDist' p hpOut ?_
    intro w hw
    have hwv : w = v := hvUnique w hw
    subst hwv
    exact mem_sphere.mp hpSphere
  · have hcard : Finset.card (G.neighborFinset u) = 2 :=
      (G.card_neighborFinset_eq_degree u).symm.trans hdeg
    obtain ⟨v, w, hvw, hmem⟩ := Finset.card_eq_two.mp hcard
    have hvAdj : G.Adj u v := (G.mem_neighborFinset u v).mp <|
      hmem.symm ▸ Finset.mem_insert_self v ({w} : Finset V)
    have hwAdj : G.Adj u w := (G.mem_neighborFinset u w).mp <|
      hmem.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self w)
    have hpair : dist (f ⟨v, hvAdj.ne'⟩) (f ⟨w, hwAdj.ne'⟩) = 1 :=
      hfDist ⟨v, hvAdj.ne'⟩ ⟨w, hwAdj.ne'⟩ <| Or.inr
        ⟨hdeg, by simpa [mem_neighborSet] using hvAdj, by simpa [mem_neighborSet] using hwAdj,
          ne_of_apply_ne Subtype.val hvw⟩
    obtain ⟨p, hpInter, hpOut⟩ := (infinite_unitSphere_inter hpair).exists_notMem_finite hfin
    refine extend_unitDistance f hfInj hfDist' p hpOut ?_
    intro x hx
    have hxvw : x = v ∨ x = w := by
      have hxFin : x ∈ G.neighborFinset u := (G.mem_neighborFinset u x).mpr hx
      have : x ∈ ({v, w} : Finset V) := by simpa [hmem] using hxFin
      simpa using this
    rcases hxvw with rfl | rfl
    · exact mem_sphere.mp hpInter.1
    · exact mem_sphere.mp hpInter.2
end Erdos1007
