-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.isExpHomR_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:10.8464+00:00
-- url     : https://prove2.me/submissions/75bf9ef3-dbe7-4d0b-85f0-f71a786f6b6b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_base_change_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_ring
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_over
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
section BC
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
variable {X : Scheme.{0}} (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp S ⟶ X)
end BC
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
section Transfer
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}
private theorem jetSubstP_apply_mk {R : Type} [CommRing R] {κ κ' : Type} (m : ℕ)
    (φ : κ → MvPolynomial κ' R) (p : MvPolynomial κ R) :
    jetSubstP m φ (Ideal.Quotient.mk (orig R κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl
private theorem bcJ_mk_lemma_2 {S' T' : Type} [CommRing S'] [CommRing T'] (g : S' →+* T') (κ : Type) (m : ℕ)
    (p : MvPolynomial κ S') :
    bcJ g κ m (Ideal.Quotient.mk (orig S' κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (MvPolynomial.map g p) := by
  rfl
private theorem jetCopy_mk_lemma_3 {R : Type} [CommRing R] (d' : ℕ) {n : ℕ} (m : ℕ) (i : Fin n)
    (p : MvPolynomial (Fin 1 × Fin d') R) :
    jetCopy d' m i (Ideal.Quotient.mk (orig R (Fin 1 × Fin d') ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun q : Fin 1 × Fin d' => (X (i, q.2) : MvPolynomial (Fin n × Fin d') R)) p) := by
  rfl
end Transfer
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution {x : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G} (hx : IsExpHomR x0 d x) :
    IsExpHomR (x0T f x0) d (xT f x0 x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun m => ?_, fun m => ?_⟩
  · have e := nat_ring f (ψ := (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m))
      (ψ' := (jetTrunc : Jet T (Fin 1 × Fin d) (m + 1) →ₐ[T] Jet T (Fin 1 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => (base_change_jet_variable f m j).symm)
    have k := nat_over f x0 (bcJ f _ (m + 1)) (bcJ_comp f _ (m + 1)) (bcJ f _ m) (bcJ_comp f _ m) _ _ e
    unfold xT
    rw [← Category.assoc, k, Category.assoc, h1 m]
  · have eS := nat_ring f
      (ψ := (jetSubstP m fun p : Fin 1 × Fin d => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) :
        Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m))
      (ψ' := (jetSubstP m fun p : Fin 1 × Fin d => X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) :
        Jet T (Fin 1 × Fin d) m →ₐ[T] Jet T (Fin 2 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => by
        rw [show zz m j = Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          show zz m j = Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          jetSubstP_apply_mk, jetSubstP_apply_mk, bcJ_mk_lemma_2]
        simp)
    have eC : ∀ i : Fin 2, _ := fun i => nat_ring f
      (ψ := (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m))
      (ψ' := (jetCopy d m i : Jet T (Fin 1 × Fin d) m →ₐ[T] Jet T (Fin 2 × Fin d) m))
      (bB := bcJ f _ m) (fun s => bcJ_C f m s) (fun j => by
        rw [show zz m j = Ideal.Quotient.mk (orig S (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          show zz m j = Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (m + 1)) (X j) from rfl,
          jetCopy_mk_lemma_3, jetCopy_mk_lemma_3, bcJ_mk_lemma_2]
        simp)
    have kS := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ eS
    have k0 := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ (eC 0)
    have k1 := nat_over f x0 (bcJ f _ m) (bcJ_comp f _ m) (bcJ f _ m) (bcJ_comp f _ m) _ _ (eC 1)
    unfold xT
    simp only [← Category.assoc, kS, k0, k1]
    simp only [Category.assoc, h2 m]
    first
    | exact Hom.comp_mul _ _ _
    | exact MonObj.comp_mul _ _ _
    | exact CategoryTheory.Hom.comp_mul _ _ _
    | simp only [Hom.comp_mul]
    | simp only [MonObj.comp_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
