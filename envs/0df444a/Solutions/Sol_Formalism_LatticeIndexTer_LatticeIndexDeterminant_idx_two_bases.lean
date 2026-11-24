-- Prove2me | solution 1 for Formalism.LatticeIndexTer.LatticeIndexDeterminant.idx_two_bases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:51.765272+00:00
-- url     : https://prove2.me/submissions/3c733692-a40f-415b-a8e9-ab4620e6b817

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_length_tower
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_arith
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_len_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.LatticeIndexDeterminant
variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]
namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant
theorem _root_.solution (b b' : Basis ι K Y) (a c0 : O) (ha : a ≠ 0) (hc0 : c0 ≠ 0)
    (h : algebraMap O K a = (b.toMatrix b').det * algebraMap O K c0) :
    idx O Y (Submodule.span O (Set.range b)) (Submodule.span O (Set.range b')) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O c0).toNat : ℤ) := by
  have hinjK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hM : (b.toMatrix b').det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact ha (hinjK (by rw [h, map_zero]))
  obtain ⟨⟨c, hc⟩, hcI⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : ι × ι => b.toMatrix b' p.1 p.2)
  have hc0' : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcI' : ∀ i j, ∃ o : O, algebraMap O K o = c • b.repr (b' j) i := by
    intro i j
    obtain ⟨o, ho⟩ := hcI (i, j)
    exact ⟨o, ho⟩
  choose o ho using hcI'
  let w : ι → Y := fun j => c • b' j
  have hw : ∀ j, w j ∈ Submodule.span O (Set.range b) := by
    intro j
    show c • b' j ∈ _
    rw [← b.sum_repr (b' j), Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_assoc, ← ho i j, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw' : ∀ j, w j ∈ Submodule.span O (Set.range b') :=
    fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmat : ∀ e : Basis ι K Y, e.toMatrix w = algebraMap O K c • e.toMatrix b' := by
    intro e
    ext i j
    simp only [Basis.toMatrix_apply, w, Matrix.smul_apply, smul_eq_mul]
    rw [← algebraMap_smul K c (b' j), map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hcK : algebraMap O K c ≠ 0 := (map_ne_zero_iff _ hinjK).2 hc0'
  obtain ⟨e, he, hlen⟩ := len_span b w hw (by
    rw [hmat, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hcK) hM)
  obtain ⟨e', he', hlen'⟩ := len_span b' w hw' (by
    rw [hmat, Matrix.det_smul, Basis.toMatrix_self, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hcK)
  have hE : Submodule.span O (Set.range w) ≤
      Submodule.span O (Set.range b) ⊓ Submodule.span O (Set.range b') :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ⟨hw j, hw' j⟩)
  have t1 := length_tower (Submodule.span O (Set.range b)) (Submodule.span O (Set.range b'))
    _ _ (fun y => Submodule.mem_inf) hE
  have t2 := length_tower (Submodule.span O (Set.range b')) (Submodule.span O (Set.range b))
    _ _ (fun y => by rw [Submodule.mem_inf, and_comm]) hE
  rw [hlen] at t1
  rw [hlen'] at t2
  have hrel : e * c0 = e' * a := by
    apply hinjK
    rw [map_mul, map_mul, he, he', h, hmat, hmat, Matrix.det_smul, Matrix.det_smul,
      Basis.toMatrix_self, Matrix.det_one]
    ring
  have hv := congrArg (IsDiscreteValuationRing.addVal O) hrel
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul] at hv
  have hne : ∀ x : O, x ≠ 0 → IsDiscreteValuationRing.addVal O x ≠ ⊤ :=
    fun x hx h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero, hmat, Matrix.det_smul] at he
    exact mul_ne_zero (pow_ne_zero _ hcK) hM he.symm
  have he0' : e' ≠ 0 := by
    rintro rfl
    rw [map_zero, hmat, Matrix.det_smul, Basis.toMatrix_self, Matrix.det_one, mul_one] at he'
    exact pow_ne_zero _ hcK he'.symm
  unfold idx qlen
  exact arith _ _ _ _ _ _ _ t1 t2 hv (hne _ he0) (hne _ he0') (hne _ ha) (hne _ hc0)
end Formalism.LatticeIndexTer.LatticeIndexDeterminant
