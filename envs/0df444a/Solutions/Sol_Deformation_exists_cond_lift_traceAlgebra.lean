-- Prove2me | solution 1 for Deformation.exists_cond_lift_traceAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1f37619c-887f-5c33-acb6-bcef337a8ceb

import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_ClosedSubalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_cond_lift_traceAlgebra

open CategoryTheory Function IsLocalRing

universe u

namespace Deformation
p2m_export "Deformation" "ConjStable ReflectedByInjective conjKer mapRepn traceSubalgebra isClosed_traceSubalgebra trace_mem_traceSubalgebra traceSubalgebra_le trace_smul_eq trace_mapRepn TraceAlgebra.Descends repnFunctor repnFunctor_map repnQuotFunctor ProartinianCat ProartinianCat.isUnit_of_isUnit_val ProartinianCat.closedSubalgebraι_injective TraceAlgebra.obj TraceAlgebra.ι"
p2m_open "Deformation"

namespace SolAuxSubalgebraGL

variable {n : Type} [Fintype n] [DecidableEq n]
variable {𝓞' R : Type u} [CommRing 𝓞'] [CommRing R] [Algebra 𝓞' R]
variable {S : Subalgebra 𝓞' R}

def liftMatrix (M : Matrix n n R) (hM : ∀ i j, M i j ∈ S) : Matrix n n S :=
  Matrix.of fun i j => ⟨M i j, hM i j⟩

omit [Fintype n] [DecidableEq n] in
@[scoped simp]
lemma liftMatrix_apply_coe (M : Matrix n n R) (hM : ∀ i j, M i j ∈ S) (i j : n) :
    (liftMatrix M hM i j : R) = M i j := rfl

omit [Fintype n] [DecidableEq n] in

lemma liftMatrix_map_val (M : Matrix n n R) (hM : ∀ i j, M i j ∈ S) :
    (liftMatrix M hM).map (S.val.toRingHom) = M := by
  ext i j
  rfl

lemma coe_det_liftMatrix (M : Matrix n n R) (hM : ∀ i j, M i j ∈ S) :
    ((liftMatrix M hM).det : R) = M.det :=
  calc ((liftMatrix M hM).det : R) = S.val.toRingHom (liftMatrix M hM).det := rfl
    _ = ((liftMatrix M hM).map S.val.toRingHom).det := RingHom.map_det _ _
    _ = M.det := by rw [liftMatrix_map_val]

lemma map_val_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := n) S.val.toRingHom) :=
  Units.map_injective fun _ _ h =>
    Matrix.ext fun i j => Subtype.val_injective (congrArg (fun P => P i j) h)

variable (hS : ∀ x : S, IsUnit (x : R) → IsUnit x)

include hS in

noncomputable def lift (M : GL n R) (hM : ∀ i j, (M : Matrix n n R) i j ∈ S) : GL n S :=
  Matrix.GeneralLinearGroup.mk'' (liftMatrix (M : Matrix n n R) hM) <| by
    refine hS _ ?_
    rw [coe_det_liftMatrix]
    exact (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit

@[scoped simp]
lemma map_lift (M : GL n R) (hM : ∀ i j, (M : Matrix n n R) i j ∈ S) :
    Matrix.GeneralLinearGroup.map S.val.toRingHom (lift hS M hM) = M := by
  ext i j
  rfl

variable {G : Type u} [Group G] [TopologicalSpace G]
variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in

private lemma continuous_entry (ρ : G →ₜ* GL n R) (i j : n) :
    Continuous fun σ => (ρ σ : Matrix n n R) i j :=
  (Units.continuous_val.comp (map_continuous ρ)).matrix_elem i j

omit [IsTopologicalRing R] in

private lemma continuous_inv_entry (ρ : G →ₜ* GL n R) (i j : n) :
    Continuous fun σ => (((ρ σ)⁻¹ : GL n R) : Matrix n n R) i j :=
  (Units.continuous_coe_inv.comp (map_continuous ρ)).matrix_elem i j

omit [IsTopologicalRing R] in
include hS in

theorem existsUnique_repnLift (ρ : G →ₜ* GL n R)
    (hρ : ∀ (σ : G) (i j : n), (ρ σ : Matrix n n R) i j ∈ S) :
    ∃! ρ' : G →ₜ* GL n S,
      ∀ σ, Matrix.GeneralLinearGroup.map S.val.toRingHom (ρ' σ) = ρ σ := by
  refine ⟨⟨MonoidHom.mk' (fun σ => lift hS (ρ σ) (hρ σ)) fun σ τ => map_val_injective ?_,
    ?_⟩, fun σ => map_lift hS _ _, fun ρ'' hρ'' => ?_⟩

  · rw [map_mul (Matrix.GeneralLinearGroup.map S.val.toRingHom)]
    simp only [map_lift]
    exact map_mul ρ σ τ

  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact continuous_matrix fun i j => (continuous_entry ρ i j).subtype_mk _
    · refine continuous_matrix fun i j => ?_

      refine continuous_induced_rng.mpr ?_
      refine (continuous_inv_entry ρ i j).congr fun σ => ?_
      have h1 : Matrix.GeneralLinearGroup.map S.val.toRingHom
          ((lift hS (ρ σ) (hρ σ))⁻¹ : GL n S) = ((ρ σ)⁻¹ : GL n R) := by
        rw [map_inv, map_lift]
      exact (congrArg (fun P : GL n R => (P : Matrix n n R) i j) h1).symm

  · refine ContinuousMonoidHom.ext fun σ => ?_
    exact map_val_injective ((hρ'' σ).trans (map_lift hS _ _).symm)

end SolAuxSubalgebraGL
p2m_reactivate "P2MW.S_Deformation_exists_cond_lift_traceAlgebra.Deformation.SolAuxSubalgebraGL"

section SolAuxTrace

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞]

p2m_open "Deformation.ProartinianCat"

lemma traceSubalgebra_eq_top_of_mapRepn_smul {A T : ProartinianCat 𝓞}
    [CompactSpace T] {ι : T ⟶ A} (hinj : Function.Injective ι.hom)
    {ρ' : G →ₜ* GL n A} {σ : G →ₜ* GL n T} {γ : ConjAct (GL n A)}
    (hmapι : mapRepn n G 𝓞 ι σ = γ • ρ')
    (himage : ∀ t : T, ι.hom t ∈ traceSubalgebra 𝓞 ρ') :
    traceSubalgebra 𝓞 σ = ⊤ := by
  rw [eq_top_iff]
  intro t _

  set V : Subalgebra 𝓞 A := Subalgebra.map ι.hom.toAlgHom (traceSubalgebra 𝓞 σ) with hV
  have hVclosed : IsClosed (V : Set A) := by
    have h1 : (V : Set A) = ⇑ι.hom '' ((traceSubalgebra 𝓞 σ :
        Subalgebra 𝓞 T) : Set T) := by
      ext a
      constructor
      · intro ha
        obtain ⟨w, hw, hweq⟩ := Subalgebra.mem_map.mp ha
        exact ⟨w, hw, hweq⟩
      · rintro ⟨w, hw, hweq⟩
        exact Subalgebra.mem_map.mpr ⟨w, hw, hweq⟩
    rw [h1]
    exact (((isClosed_traceSubalgebra σ).isCompact).image (map_continuous ι.hom)).isClosed
  have hVmem : ∀ x : G, Matrix.trace ((ρ' x : GL n A) : Matrix n n A) ∈ V := by
    intro x
    refine Subalgebra.mem_map.mpr
      ⟨Matrix.trace ((σ x : GL n T) : Matrix n n T), trace_mem_traceSubalgebra σ x, ?_⟩

    calc ι.hom.toAlgHom (Matrix.trace ((σ x : GL n T) : Matrix n n T))
        = ι.hom (Matrix.trace ((σ x : GL n T) : Matrix n n T)) := rfl
      _ = Matrix.trace ((mapRepn n G 𝓞 ι σ x : GL n A) : Matrix n n A) :=
          (trace_mapRepn ι σ x).symm
      _ = Matrix.trace (((γ • ρ') x : GL n A) : Matrix n n A) := by rw [hmapι]
      _ = Matrix.trace ((ρ' x : GL n A) : Matrix n n A) := trace_smul_eq γ ρ' x
  have hle : traceSubalgebra 𝓞 ρ' ≤ V := traceSubalgebra_le ρ' hVclosed hVmem
  obtain ⟨w, hw, hweq⟩ := Subalgebra.mem_map.mp (hle (himage t))
  have hwt : w = t := hinj hweq
  exact hwt ▸ hw

end SolAuxTrace
p2m_reactivate "P2MW.S_Deformation_exists_cond_lift_traceAlgebra.Deformation.SolAuxSubalgebraGL"

end Deformation
p2m_reactivate "P2MW.S_Deformation_exists_cond_lift_traceAlgebra.Deformation.SolAuxSubalgebraGL P2MW.S_Deformation_exists_cond_lift_traceAlgebra.Deformation"

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in

theorem solution {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (IsLocalRing.ResidueField 𝓞)]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (hconj : Deformation.ConjStable n F)
    (hrefl : Deformation.ReflectedByInjective n F) {A : Deformation.ProartinianCat 𝓞} {ρ' : G →ₜ* GL n A}
    (hρ' : ρ' ∈ F.obj A) (hdesc : Deformation.TraceAlgebra.Descends ρ') :
    ∃ σ : G →ₜ* GL n (Deformation.TraceAlgebra.obj ρ'),
      σ ∈ F.obj (Deformation.TraceAlgebra.obj ρ') ∧
      Deformation.traceSubalgebra 𝓞 σ = ⊤ ∧
      (Quotient.mk'' (Deformation.mapRepn n G 𝓞 (Deformation.TraceAlgebra.ι ρ') σ) :
        (Deformation.repnQuotFunctor n G 𝓞).obj A) = Quotient.mk'' ρ' := by
  classical
  obtain ⟨γ, hγ, hentries⟩ := hdesc
  obtain ⟨σ, hσ, -⟩ := Deformation.SolAuxSubalgebraGL.existsUnique_repnLift
    (S := Deformation.traceSubalgebra 𝓞 ρ')
    (fun x hx => Deformation.ProartinianCat.isUnit_of_isUnit_val _ (Deformation.isClosed_traceSubalgebra ρ') x hx)
    (γ • ρ') hentries
  have hmapι : (Deformation.repnFunctor n G 𝓞).map (Deformation.TraceAlgebra.ι ρ') σ = γ • ρ' :=
    ContinuousMonoidHom.ext fun x =>
      (Deformation.repnFunctor_map G 𝓞 (Deformation.TraceAlgebra.ι ρ') σ x).trans (hσ x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · refine hrefl (Deformation.TraceAlgebra.ι ρ')
      (Deformation.ProartinianCat.closedSubalgebraι_injective (Deformation.traceSubalgebra 𝓞 ρ')
        (Deformation.isClosed_traceSubalgebra ρ')) ?_
    rw [hmapι]
    exact hconj hρ' hγ
  · exact Deformation.traceSubalgebra_eq_top_of_mapRepn_smul
      (Deformation.ProartinianCat.closedSubalgebraι_injective (Deformation.traceSubalgebra 𝓞 ρ')
        (Deformation.isClosed_traceSubalgebra ρ'))
      hmapι fun t => t.2
  · calc (Quotient.mk'' (Deformation.mapRepn n G 𝓞 (Deformation.TraceAlgebra.ι ρ') σ) :
          (Deformation.repnQuotFunctor n G 𝓞).obj A)
        = Quotient.mk'' (γ • ρ') := congrArg _ hmapι
      _ = Quotient.mk'' ρ' := Quotient.sound'
          (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit ρ' (⟨γ, hγ⟩ : Deformation.conjKer (n := n) A)))

end S_Deformation_exists_cond_lift_traceAlgebra
end P2MW
export P2MW.S_Deformation_exists_cond_lift_traceAlgebra (solution)
