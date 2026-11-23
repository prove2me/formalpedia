-- Prove2me | solution 1 for Formalism.HN.Rerealization.covol_rk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:09.946315+00:00
-- url     : https://prove2.me/submissions/ef9868de-e882-43d7-b97a-2381657b7fc9

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Theorems.Thm_Formalism_HN_Rerealization_eq_of_eq
import Theorems.Thm_Formalism_HN_Rerealization_inner_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField
noncomputable section
namespace Formalism.HN
namespace Rerealization
section Lat
variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
private theorem det_gram_basis_eq' {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ F)
    (C C' : Module.Basis ι ℤ L) :
    (Matrix.gram ℝ (fun i => ((C' i : L) : F))).det = (Matrix.gram ℝ (fun i => ((C i : L) : F))).det := by
  set P : Matrix ι ι ℝ := (C.toMatrix C').map (Int.cast : ℤ → ℝ) with hP
  have hC' : ∀ i, ((C' i : L) : F) = ∑ k, P k i • ((C k : L) : F) := by
    intro i
    have e := congrArg (fun w : L => (w : F)) (C.sum_repr (C' i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP, Matrix.map_apply, Module.Basis.toMatrix_apply, Int.cast_smul_eq_zsmul]
  have hG : Matrix.gram ℝ (fun i => ((C' i : L) : F)) =
      P.transpose * Matrix.gram ℝ (fun i => ((C i : L) : F)) * P := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hC', sum_inner,
      inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    first
      | (refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_;
          rw [real_inner_comm]; ring)
  have hdet : (C.toMatrix C').det * (C'.toMatrix C).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hPd : P.det = ((C.toMatrix C').det : ℝ) := by
    rw [hP]
    first
      | exact (Int.cast_det _).symm
      | exact ((Int.castRingHom ℝ).map_det _).symm
  have hsq : P.det ^ 2 = 1 := by
    rw [hPd]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;> simp [h]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ∀ a b : ℝ, a * b * a = a ^ 2 * b from fun a b => by ring, hsq, one_mul]
private theorem covol_eq_of_inner_preserving_equiv (L1 : Submodule ℤ E) (L2 : Submodule ℤ F) [DiscreteTopology L1]
    [DiscreteTopology L2] (τ : L1 ≃ₗ[ℤ] L2)
    (hτ : ∀ x y : L1, inner ℝ ((τ x : L2) : F) ((τ y : L2) : F) = inner ℝ (x : E) (y : E)) :
    Formalism.F.covol L1 = Formalism.F.covol L2 := by
  have hr : Module.finrank ℤ L1 = Module.finrank ℤ L2 := τ.finrank_eq
  unfold Formalism.F.covol
  rw [dif_pos ‹DiscreteTopology L1›, dif_pos ‹DiscreteTopology L2›]
  congr 1
  let B : Module.Basis (Fin (Module.finrank ℤ L2)) ℤ L2 :=
    ((Module.finBasis ℤ L1).map τ).reindex (finCongr hr)
  have h1 : Matrix.gram ℝ (fun i => ((Module.finBasis ℤ L1 i : L1) : E)) =
      (Matrix.gram ℝ (fun i => ((B i : L2) : F))).submatrix (finCongr hr) (finCongr hr) := by
    ext i j
    simp [B, Matrix.gram, hτ]
  rw [h1, Matrix.det_submatrix_equiv_self, det_gram_basis_eq' L2 (Module.finBasis ℤ L2) B]
end Lat
section Abs
variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
end Abs
end Rerealization
end Formalism.HN
end
end

set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.Rerealization
variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace Formalism.HN.Rerealization
theorem _root_.solution (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G)
    (hα : DiscreteTopology (H.map α).toIntSubmodule)
    (hβ : DiscreteTopology (H.map β).toIntSubmodule) :
    Formalism.F.covol (H.map β).toIntSubmodule = Formalism.F.covol (H.map α).toIntSubmodule ∧
      Formalism.F.rk (H.map β).toIntSubmodule = Formalism.F.rk (H.map α).toIntSubmodule := by
  haveI := hα
  haveI := hβ
  have ex : ∀ y : (H.map α).toIntSubmodule, ∃ g ∈ H, α g = (y : E) := fun y =>
    AddSubgroup.mem_map.mp y.2
  let τf : (H.map α).toIntSubmodule →+ (H.map β).toIntSubmodule :=
    { toFun := fun y => ⟨β (ex y).choose, AddSubgroup.mem_map.mpr ⟨_, (ex y).choose_spec.1, rfl⟩⟩
      map_zero' := by
        apply Subtype.ext
        show β (ex 0).choose = 0
        rw [← map_zero β]
        exact eq_of_eq α β hn (by simp [(ex 0).choose_spec.2])
      map_add' := fun y z => by
        apply Subtype.ext
        show β (ex (y + z)).choose = β (ex y).choose + β (ex z).choose
        rw [← map_add]
        exact eq_of_eq α β hn
          (by simp [(ex (y + z)).choose_spec.2, (ex y).choose_spec.2, (ex z).choose_spec.2]) }
  have hval : ∀ (y : (H.map α).toIntSubmodule) (g : G), α g = (y : E) → ((τf y : (H.map β).toIntSubmodule) : F) = β g := fun y g hg =>
    eq_of_eq α β hn (((ex y).choose_spec.2).trans hg.symm)
  have hnorm : ∀ y, ‖((τf y : (H.map β).toIntSubmodule) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [hval y _ (ex y).choose_spec.2, hn, (ex y).choose_spec.2]
  have hinj : Function.Injective τf := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have : ‖(y : E)‖ = 0 := by rw [← hnorm, hy]; simp
    exact Subtype.ext (norm_eq_zero.mp this)
  have hsurj : Function.Surjective τf := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨⟨α g, AddSubgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩, Subtype.ext (hval _ g rfl)⟩
  let τ : (H.map α).toIntSubmodule ≃ₗ[ℤ] (H.map β).toIntSubmodule :=
    (AddEquiv.ofBijective τf ⟨hinj, hsurj⟩).toIntLinearEquiv
  have hτ : ∀ x y : (H.map α).toIntSubmodule, inner ℝ ((τ x : (H.map β).toIntSubmodule) : F)
      ((τ y : (H.map β).toIntSubmodule) : F) = inner ℝ (x : E) (y : E) := by
    intro x y
    exact inner_eq ((H.map α).toIntSubmodule.subtype.toAddMonoidHom)
      (((H.map β).toIntSubmodule.subtype.toAddMonoidHom).comp τf) hnorm x y
  exact ⟨(covol_eq_of_inner_preserving_equiv _ _ τ hτ).symm, τ.finrank_eq.symm⟩
end Formalism.HN.Rerealization
