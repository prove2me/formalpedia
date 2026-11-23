-- Prove2me | solution 1 for Formalism.ELL.WeierstrassCoordinateSubstitution.assoc_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:28.053188+00:00
-- url     : https://prove2.me/submissions/5089e99a-de80-442c-b5a0-f89beeb1d0f8

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_ne_of_hom
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_eq_of_xy
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_chord_add
import Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
end WeierstrassCoordinateSubstitution
end Formalism.ELL
namespace Formalism.ELL
namespace WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
private theorem subst_subst_pair' {τ υ : Type} (F : MvPowerSeries (Fin 2) K)
    (a b : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (v : τ → MvPowerSeries υ K)
    (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (F.subst ![a, b]) =
      F.subst ![MvPowerSeries.subst v a, MvPowerSeries.subst v b] := by
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [ha, hb])
  rw [MvPowerSeries.subst_comp_subst_apply hab hv]
  congr 1
  funext i
  fin_cases i <;> rfl
private theorem subst_X_X_ne_zero (F : MvPowerSeries (Fin 2) K)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1) (i j : Fin 3)
    (v : Fin 3 → MvPowerSeries (Fin 2) K) (hv0 : ∀ k, MvPowerSeries.constantCoeff (v k) = 0)
    (hi : v i = MvPowerSeries.X 0) (hj : v j = MvPowerSeries.X 1) :
    F.subst ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) K), MvPowerSeries.X j] ≠ 0 := by
  intro h
  have hv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  have h1 := congrArg (MvPowerSeries.subst v) h
  rw [subst_subst_pair' F _ _ (by simp) (by simp) v hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv, hi, hj] at h1
  have h0 : MvPowerSeries.subst v (0 : MvPowerSeries (Fin 3) K) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hv, map_zero]
  have e : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext k
    fin_cases k <;> rfl
  rw [h0, e, MvPowerSeries.subst_self, id_eq] at h1
  rw [h1] at hF1
  simp at hF1
end WeierstrassCoordinateSubstitution
end Formalism.ELL
end
end

set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassCoordinateSubstitution
theorem _root_.solution (hS : WChordSubst.{u}) (hP : WPoint.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) {u : PowerSeries K} (hwu : w = X ^ 3 * u)
    (hu : constantCoeff u = 1) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) :
    F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1],
        MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
        F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by
  classical
  have cX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have nX : ∀ i : Fin 3, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ≠ 0 :=
    fun i => X_ne_zero' i
  have cSub : ∀ a b : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (F.subst ![a, b]) = 0 := by
    intro a b ha hb
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [ha, hb]))
      (fun i => by fin_cases i <;> simp [ha, hb]) hF0
  have ne_of : ∀ (v : Fin 3 → MvPowerSeries (Fin 3) K),
      (∀ i, MvPowerSeries.constantCoeff (v i) = 0) →
      ∀ s t : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 →
      MvPowerSeries.constantCoeff t = 0 → s ≠ 0 → t ≠ 0 → MvPowerSeries.subst v s = 0 →
      MvPowerSeries.subst v t ≠ 0 → xOf w s ≠ xOf w t := by
    intro v hv s t hs0 ht0 hs ht h1 h2
    have hv' := MvPowerSeries.hasSubst_of_constantCoeff_zero hv
    exact xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hv') s t hs0 ht0 hs ht
      (by rw [MvPowerSeries.coe_substAlgHom]; exact h1)
      (by rw [MvPowerSeries.coe_substAlgHom]; exact h2)
  have g01 : F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] ≠ 0 :=
    subst_X_X_ne_zero F hF1 0 1 ![MvPowerSeries.X 0, MvPowerSeries.X 1, 0]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have g12 : F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] ≠ 0 :=
    subst_X_X_ne_zero F hF1 1 2 ![0, MvPowerSeries.X 0, MvPowerSeries.X 1]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have c01 := cSub _ _ (cX 0) (cX 1)
  have c12 := cSub _ _ (cX 1) (cX 2)
  have hv1 : ∀ i, MvPowerSeries.constantCoeff
      ((![0, MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv2 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv3 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, 0, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have ne1 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 1) := by
    refine ne_of _ hv1 _ _ (cX 0) (cX 1) (nX 0) (nX 1) ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; rfl
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; exact nX 1
  have ne2 : xOf w (F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]) ≠
      xOf w (MvPowerSeries.X 2) := by
    refine Ne.symm (ne_of _ hv2 _ _ (cX 2) c01 (nX 2) g01 ?_ ?_)
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2)]; rfl
    · rw [subst_subst_pair' F _ _ (cX 0) (cX 1) _ (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2)]
      exact g01
  have ne3 : xOf w (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 2) := by
    refine ne_of _ hv3 _ _ (cX 1) (cX 2) (nX 1) (nX 2) ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv3)]; rfl
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv3)]; exact nX 2
  have ne4 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠
      xOf w (F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]) := by
    refine ne_of _ hv1 _ _ (cX 0) c12 (nX 0) g12 ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; rfl
    · rw [subst_subst_pair' F _ _ (cX 1) (cX 2) _ (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]
      exact g12
  have ch1 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) (cX 1) (nX 0) (nX 1) ne1
  have ch2 := hS K W w hw F hF0 hch (Fin 3) _ _ c01 (cX 2) g01 (nX 2) ne2
  have ch3 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 1) (cX 2) (nX 1) (nX 2) ne3
  have ch4 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) c12 (nX 0) g12 ne4
  have p0 := hP K W w hw (Fin 3) _ (cX 0) (nX 0)
  have p1 := hP K W w hw (Fin 3) _ (cX 1) (nX 1)
  have p2 := hP K W w hw (Fin 3) _ (cX 2) (nX 2)
  have p01 := hP K W w hw (Fin 3) _ c01 g01
  have p12 := hP K W w hw (Fin 3) _ c12 g12
  obtain ⟨h01, e1⟩ := chord_add _ _ _ p0 p1 ne1 ch1
  obtain ⟨hL, e2⟩ := chord_add _ _ _ p01 p2 ne2 ch2
  obtain ⟨h12, e3⟩ := chord_add _ _ _ p1 p2 ne3 ch3
  obtain ⟨hR, e4⟩ := chord_add _ _ _ p0 p12 ne4 ch4
  have key := e2.symm.trans (((congrArg (· + _) e1).symm.trans
    ((add_assoc _ _ _).trans (congrArg (_ + ·) e3))).trans e4)
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at key
  exact eq_of_xy hwu hu _ _ (cSub _ _ c01 (cX 2)) (cSub _ _ (cX 0) c12) key.1 key.2
end Formalism.ELL.WeierstrassCoordinateSubstitution
