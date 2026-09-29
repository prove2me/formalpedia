-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.mem_typePreserving_iff_even_of_det_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8853effa-c3a1-5cbf-90fb-a892993e0a6a

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Theorems.Thm_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
import Theorems.Thm_CerednikDrinfeld_BruhatTits_dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
p2m_attr_erase "simp" "LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow.CerednikDrinfeld CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow.CerednikDrinfeld.BruhatTits CerednikDrinfeld.Mumford LT.LatticeTree"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "pgl_mk_smul tree BruhatTits.tree Mumford.typePreserving"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree pgl_mk_smul tree_connected_and_colorable_two dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit"
namespace Hinge
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

variable {R₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
variable {K₀ : Type} [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

theorem algebraMap_ne_zero {x : R₀} (hx : x ≠ 0) : algebraMap R₀ K₀ x ≠ 0 := fun h =>
  hx ((IsFractionRing.to_map_eq_zero_iff (R := R₀) (K := K₀)).1 h)

theorem scalarGL_smul (c : K₀ˣ) (x : Vertex R₀ K₀) : scalarGL c • x = x :=
  isFixedVertex_scalarGL c x

theorem scalarGL_mul_smul (c : K₀ˣ) (g : GL (Fin 2) K₀) (x : Vertex R₀ K₀) : (scalarGL c * g) • x = g • x := by
  rw [mul_smul, scalarGL_smul]

theorem scalarGL_mul_apply (c : K₀ˣ) (g : GL (Fin 2) K₀) (i j : Fin 2) :
    ((scalarGL c * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j = (c : K₀) * (g : Matrix (Fin 2) (Fin 2) K₀) i j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
    smul_eq_mul]

theorem det_scalarGL_mul (c : K₀ˣ) (g : GL (Fin 2) K₀) :
    Matrix.det ((scalarGL c * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
      (c : K₀) ^ 2 * Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul,
    Fintype.card_fin]

theorem not_dvd_unit {ϖ₀ : R₀} (hϖ₀ : Irreducible ϖ₀) (w : R₀ˣ) : ¬ ϖ₀ ∣ (w : R₀) := fun h =>
  hϖ₀.not_isUnit (isUnit_of_dvd_unit h w.isUnit)

theorem natCast_dist_eq_of_det_eq (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (n : ℕ) :
    ∀ (a : Matrix (Fin 2) (Fin 2) R₀) (w : R₀ˣ), a.det = (w : R₀) * ϖ₀ ^ n →
      ∀ g : GL (Fin 2) K₀, (g : Matrix (Fin 2) (Fin 2) K₀) = a.map (algebraMap R₀ K₀) →
        ((tree R₀ K₀).dist (stdVertex R₀ K₀) (g • stdVertex R₀ K₀) : ZMod 2) = (n : ZMod 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a w ha g hg
  by_cases hu : ∃ i j : Fin 2, IsUnit (a i j)
  · obtain ⟨i, j, ⟨w', hw'⟩⟩ := hu
    have hint : ∀ i j, IsLocalization.IsInteger R₀ ((g : Matrix (Fin 2) (Fin 2) K₀) i j) := by
      intro i j; rw [hg, Matrix.map_apply]; exact ⟨a i j, rfl⟩
    have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀) =
        algebraMap R₀ K₀ w * algebraMap R₀ K₀ ϖ₀ ^ n := by
      rw [hg, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ha, map_mul, map_pow]
    have hunit : ∃ i j : Fin 2, ∃ w : R₀ˣ, (g : Matrix (Fin 2) (Fin 2) K₀) i j = algebraMap R₀ K₀ w :=
      ⟨i, j, w', by rw [hg, Matrix.map_apply, hw']⟩
    rw [dist_stdVertex_smul_stdVertex_eq_of_isInteger_of_det_eq_of_isUnit R₀ K₀ ϖ₀ hϖ₀ g hint n w hdet hunit]
  · push_neg at hu
    have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hϖ₀
    have hdvd : ∀ i j : Fin 2, ∃ c : R₀, a i j = ϖ₀ * c := by
      intro i j
      have hmem : a i j ∈ IsLocalRing.maximalIdeal R₀ := (IsLocalRing.mem_maximalIdeal _).2 (hu i j)
      rw [hmax, Ideal.mem_span_singleton'] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, by rw [← hc, mul_comm]⟩
    choose f hf using hdvd

    have hdet2 : ϖ₀ ^ 2 * (Matrix.of f).det = (w : R₀) * ϖ₀ ^ n := by
      rw [← ha, Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [Matrix.of_apply]
      rw [hf 0 0, hf 0 1, hf 1 0, hf 1 1]; ring
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := by
      rcases n with _ | n
      · exact absurd ⟨ϖ₀ * (Matrix.of f).det, by rw [← mul_assoc, ← pow_two, hdet2, pow_zero, mul_one]⟩
          (not_dvd_unit hϖ₀ w)
      rcases n with _ | n'
      · refine absurd ⟨(Matrix.of f).det, mul_left_cancel₀ hϖ₀.ne_zero ?_⟩ (not_dvd_unit hϖ₀ w)
        rw [← mul_assoc, ← pow_two, hdet2, pow_one, mul_comm]
      · exact ⟨n', rfl⟩
    have hdet' : (Matrix.of f).det = (w : R₀) * ϖ₀ ^ n' := by
      have h2 : ϖ₀ ^ 2 * (Matrix.of f).det = ϖ₀ ^ 2 * ((w : R₀) * ϖ₀ ^ n') := by rw [hdet2]; ring
      exact mul_left_cancel₀ (pow_ne_zero 2 hϖ₀.ne_zero) h2

    set c : K₀ˣ := Units.mk0 (algebraMap R₀ K₀ ϖ₀) (algebraMap_ne_zero hϖ₀.ne_zero) with hc
    have hg' : ((scalarGL c⁻¹ * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) =
        (Matrix.of f).map (algebraMap R₀ K₀) := by
      ext i j
      rw [scalarGL_mul_apply, hg, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hf i j, map_mul,
        Units.val_inv_eq_inv_val, hc, Units.val_mk0, inv_mul_cancel_left₀ (algebraMap_ne_zero hϖ₀.ne_zero)]
    have hsm : (scalarGL c⁻¹ * g) • stdVertex R₀ K₀ = g • stdVertex R₀ K₀ := scalarGL_mul_smul _ _ _
    rw [← hsm, ih n' (by omega) (Matrix.of f) w hdet' _ hg', Nat.cast_add, Nat.cast_ofNat]
    rw [show (2 : ZMod 2) = 0 from rfl, add_zero]

theorem natCast_dist_eq_intCast (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (m : GL (Fin 2) K₀) (u : R₀ˣ) (k : ℤ)
    (hdet : Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) = algebraMap R₀ K₀ u * algebraMap R₀ K₀ ϖ₀ ^ k) :
    ((tree R₀ K₀).dist (stdVertex R₀ K₀) (m • stdVertex R₀ K₀) : ZMod 2) = ((k : ℤ) : ZMod 2) := by

  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R₀)
    (fun ij : Fin 2 × Fin 2 => (m : Matrix (Fin 2) (Fin 2) K₀) ij.1 ij.2)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨nb, wb, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ₀

  set N : ℕ := nb + k.natAbs with hN
  have hϖK : algebraMap R₀ K₀ ϖ₀ ≠ 0 := algebraMap_ne_zero hϖ₀.ne_zero
  set c : K₀ˣ := Units.mk0 (algebraMap R₀ K₀ ϖ₀ ^ N) (pow_ne_zero N hϖK) with hc

  have hint : ∀ i j : Fin 2, ∃ y : R₀, algebraMap R₀ K₀ y = (c : K₀) * (m : Matrix (Fin 2) (Fin 2) K₀) i j := by
    intro i j
    obtain ⟨y, hy⟩ := hbint (i, j)
    refine ⟨(wb⁻¹ : R₀ˣ) * ϖ₀ ^ k.natAbs * y, ?_⟩
    simp only at hy
    rw [map_mul, hy, Algebra.smul_def, hbeq, hc, Units.val_mk0, hN, map_mul, map_mul, map_pow, map_pow, pow_add]
    rw [← mul_assoc, ← mul_assoc, mul_assoc (algebraMap R₀ K₀ ↑wb⁻¹) _ (algebraMap R₀ K₀ ↑wb),
      mul_comm (algebraMap R₀ K₀ ϖ₀ ^ k.natAbs) (algebraMap R₀ K₀ ↑wb), ← mul_assoc, ← map_mul,
      Units.inv_mul, map_one, one_mul]
    ring
  choose y hy using hint
  have hg : ((scalarGL c * m : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = (Matrix.of y).map (algebraMap R₀ K₀) := by
    ext i j; rw [scalarGL_mul_apply, Matrix.map_apply, Matrix.of_apply, hy]

  have hnn : 0 ≤ 2 * (N : ℤ) + k := by
    have h1 : (k.natAbs : ℤ) = |k| := Int.natCast_natAbs k
    have h2 : -k ≤ |k| := neg_le_abs k
    have h3 : (N : ℤ) = nb + k.natAbs := by rw [hN]; push_cast; rfl
    have h4 : (0 : ℤ) ≤ nb := Int.natCast_nonneg nb
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (K : ℤ) = 2 * (N : ℤ) + k := ⟨(2 * (N : ℤ) + k).toNat, Int.toNat_of_nonneg hnn⟩
  have hdetK : (Matrix.of y).det = (u : R₀) * ϖ₀ ^ K := by
    apply IsFractionRing.injective R₀ K₀
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hg, det_scalarGL_mul, hdet, hc, Units.val_mk0, map_mul,
      map_pow, ← pow_mul', ← zpow_natCast (algebraMap R₀ K₀ ϖ₀) K, hK, zpow_add₀ hϖK,
      ← zpow_natCast (algebraMap R₀ K₀ ϖ₀) (2 * N), Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [← scalarGL_mul_smul c m, natCast_dist_eq_of_det_eq ϖ₀ hϖ₀ K (Matrix.of y) u hdetK _ hg]
  rw [show ((K : ℕ) : ZMod 2) = ((K : ℤ) : ZMod 2) by norm_cast, hK, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

end CerednikDrinfeld.BruhatTits.Hinge

open CerednikDrinfeld.BruhatTits.Hinge in
theorem solution
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    (K₀ : Type) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀)
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    (hact : ∀ (g : G) (x : LT.LatticeTree.Vertex R₀ K₀), g • x = ρ g • x)
    (g : G) (m : GL (Fin 2) K₀) (hm : ρ g = Matrix.ProjGenLinGroup.mk m)
    (u : R₀ˣ) (k : ℤ)
    (hdet : Matrix.det (m : Matrix (Fin 2) (Fin 2) K₀) = algebraMap R₀ K₀ u * algebraMap R₀ K₀ ϖ₀ ^ k) :
    g ∈ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) ↔ Even k := by
  obtain ⟨hc, hb⟩ := tree_connected_and_colorable_two R₀ K₀
  obtain ⟨-, hlaw, -⟩ := vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
    (PGL(2, K₀)) (tree R₀ K₀) hc hb (stdVertex R₀ K₀)
  have step1 : g ∈ Mumford.typePreserving G (tree R₀ K₀) (stdVertex R₀ K₀) ↔
      vertexType (tree R₀ K₀) (stdVertex R₀ K₀) (m • stdVertex R₀ K₀) = 0 := by
    rw [mem_typePreserving_iff]
    constructor
    · intro h
      have h0 := h (stdVertex R₀ K₀)
      rw [vertexType_self, hact, hm, pgl_mk_smul] at h0
      exact h0
    · intro h w
      rw [hact, hm, hlaw, pgl_mk_smul, h, zero_add]
  rw [step1, vertexType_apply, natCast_dist_eq_intCast ϖ₀ hϖ₀ m u k hdet, ZMod.intCast_eq_zero_iff_even]

end S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_mem_typePreserving_iff_even_of_det_eq_mul_zpow (solution)
