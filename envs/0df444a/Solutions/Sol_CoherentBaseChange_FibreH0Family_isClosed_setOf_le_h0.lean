-- Prove2me | solution 1 for CoherentBaseChange.FibreH0Family.isClosed_setOf_le_h0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6e3574af-80cd-5364-b8be-e4429b7a8e1e

import Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0

set_option autoImplicit false

noncomputable section

universe u v

open scoped TensorProduct
p2m_open "AlgebraicGeometry CategoryTheory Opposite CoherentBaseChange P2MW.S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0.CoherentBaseChange"

namespace CBCSol

section CoreLemma

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

theorem exists_det_submatrix_ne_zero_of_le_rank
    (M : Matrix m n K) (r : ℕ) (hrk : r + 1 ≤ M.rank) :
    ∃ (s : Fin (r + 1) → m) (t : Fin (r + 1) → n), (M.submatrix s t).det ≠ 0 := by
  classical
  obtain ⟨ιc, ac, hacinj, hcspan, hcli⟩ := exists_linearIndependent' K M.col
  haveI : Fintype ιc := Fintype.ofInjective ac hacinj
  have hcard_c : r + 1 ≤ Fintype.card ιc := by
    have hc := finrank_span_eq_card hcli
    rw [hcspan, ← Matrix.rank_eq_finrank_span_cols] at hc
    omega
  obtain ⟨ec⟩ : Nonempty (Fin (r + 1) ↪ ιc) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hcard_c)
  let t : Fin (r + 1) → n := ac ∘ ec
  have htli : LinearIndependent K (M.col ∘ t) := hcli.comp ec ec.injective
  set N : Matrix m (Fin (r + 1)) K := M.submatrix id t with hN
  have hNcol : LinearIndependent K N.col := by
    have : N.col = M.col ∘ t := by ext j i; simp [hN, Matrix.col]
    exact this ▸ htli
  have hNinj : Function.Injective (Matrix.mulVecLin N) := by
    rw [show (Matrix.mulVecLin N : (Fin (r + 1) → K) → (m → K)) = N.mulVec from rfl,
      Matrix.mulVec_injective_iff]
    exact hNcol
  have hNrk : N.rank = r + 1 := by
    rw [Matrix.rank_eq_finrank_span_cols, ← Matrix.range_mulVecLin,
      LinearMap.finrank_range_of_inj hNinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hrow_span : Module.finrank K (Submodule.span K (Set.range N.row)) = r + 1 := by
    rw [← Matrix.rank_eq_finrank_span_row, hNrk]
  obtain ⟨ιr, ar, harinj, hrspan, hrli⟩ := exists_linearIndependent' K N.row
  haveI : Fintype ιr := Fintype.ofInjective ar harinj
  have hcard_r : Fintype.card ιr = Fintype.card (Fin (r + 1)) := by
    have hc := finrank_span_eq_card hrli
    rw [hrspan, hrow_span] at hc
    rw [Fintype.card_fin]; omega
  let er : Fin (r + 1) ≃ ιr := (Fintype.equivOfCardEq hcard_r).symm
  let s : Fin (r + 1) → m := ar ∘ er
  have hsli : LinearIndependent K (N.submatrix s id).row := by
    have : (N.submatrix s id).row = (N.row ∘ ar) ∘ er := by ext i j; rfl
    exact this ▸ hrli.comp er er.injective
  refine ⟨s, t, ?_⟩
  have hsub : M.submatrix s t = N.submatrix s id := by
    ext i j; simp [hN, Matrix.submatrix_apply]
  rw [hsub]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hsli)).ne_zero

theorem rank_le_of_det_submatrix_eq_zero
    (M : Matrix m n K) (r : ℕ)
    (hminors : ∀ (s : Fin (r + 1) → m) (t : Fin (r + 1) → n), (M.submatrix s t).det = 0) :
    M.rank ≤ r := by
  by_contra hlt
  obtain ⟨s, t, hne⟩ := exists_det_submatrix_ne_zero_of_le_rank M r (by omega)
  exact hne (hminors s t)

end CoreLemma

abbrev κ {R : Type u} [CommRing R] (𝔭 : PrimeSpectrum R) : Type u := 𝔭.asIdeal.ResidueField

end CBCSol

namespace CoherentBaseChange
p2m_export "CoherentBaseChange" "FibreH0Family TwoTermComplex"
namespace TwoTermComplex
p2m_export "CoherentBaseChange.TwoTermComplex" "fibreH0 C0 d C1"
p2m_open "CoherentBaseChange.TwoTermComplex CoherentBaseChange"

open CBCSol

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

private def _root_.CoherentBaseChange.TwoTermComplex.fibreRank (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭)))

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreRank"
private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreH0_add_fibreRank (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 + G.fibreRank 𝔭 = Module.finrank (κ 𝔭) (κ 𝔭 ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange (κ 𝔭))
  show Module.finrank (κ 𝔭) (LinearMap.ker (G.d.baseChange (κ 𝔭)))
      + Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreH0_add_fibreRank"

private theorem _root_.CoherentBaseChange.TwoTermComplex.setOf_le_fibreH0_eq [StrongRankCondition R] (n : ℕ) :
    {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭}
      = {𝔭 | G.fibreRank 𝔭 + n ≤ Module.finrank R G.C0} := by
  ext 𝔭
  have h := G.fibreH0_add_fibreRank 𝔭
  rw [Module.finrank_baseChange] at h
  simp only [Set.mem_setOf_eq]
  omega

p2m_export "CoherentBaseChange.TwoTermComplex" "setOf_le_fibreH0_eq"

theorem isClosed_add_le_const {X : Type*} [TopologicalSpace X] {f : X → ℕ}
    (hf : ∀ r, IsClosed {x | f x ≤ r}) (n c : ℕ) :
    IsClosed {x | f x + n ≤ c} := by
  rcases le_or_gt n c with hle | hgt
  · have heq : {x | f x + n ≤ c} = {x | f x ≤ c - n} := by
      ext x; simp only [Set.mem_setOf_eq]; omega
    rw [heq]; exact hf (c - n)
  · have heq : {x | f x + n ≤ c} = (∅ : Set X) := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; omega
    rw [heq]; exact isClosed_empty

private abbrev _root_.CoherentBaseChange.TwoTermComplex.b0 : Module.Basis (Module.Free.ChooseBasisIndex R G.C0) R G.C0 :=
  Module.Free.chooseBasis R G.C0

p2m_export "CoherentBaseChange.TwoTermComplex" "b0"

private abbrev _root_.CoherentBaseChange.TwoTermComplex.b1 : Module.Basis (Module.Free.ChooseBasisIndex R G.C1) R G.C1 :=
  Module.Free.chooseBasis R G.C1

p2m_export "CoherentBaseChange.TwoTermComplex" "b1"

private def _root_.CoherentBaseChange.TwoTermComplex.Md : Matrix (Module.Free.ChooseBasisIndex R G.C1) (Module.Free.ChooseBasisIndex R G.C0) R :=
  LinearMap.toMatrix G.b0 G.b1 G.d

p2m_export "CoherentBaseChange.TwoTermComplex" "Md"

private theorem _root_.CoherentBaseChange.TwoTermComplex.fibreRank_eq_rank_map (𝔭 : PrimeSpectrum R) :
    G.fibreRank 𝔭 = (G.Md.map (algebraMap R (κ 𝔭))).rank := by
  classical
  show Module.finrank (κ 𝔭) (LinearMap.range (G.d.baseChange (κ 𝔭))) = _
  have key := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (Algebra.TensorProduct.basis (κ 𝔭) G.b0)
      (Algebra.TensorProduct.basis (κ 𝔭) G.b1) (G.d.baseChange (κ 𝔭)))
    (Algebra.TensorProduct.basis (κ 𝔭) G.b1)
    (Algebra.TensorProduct.basis (κ 𝔭) G.b0)
  rw [Matrix.toLin_toMatrix] at key
  rw [← key, LinearMap.toMatrix_baseChange]
  rfl

p2m_export "CoherentBaseChange.TwoTermComplex" "fibreRank_eq_rank_map"

private def _root_.CoherentBaseChange.TwoTermComplex.minors (r : ℕ) : Set R :=
  {x | ∃ (s : Fin (r + 1) → Module.Free.ChooseBasisIndex R G.C1)
         (t : Fin (r + 1) → Module.Free.ChooseBasisIndex R G.C0),
    x = (G.Md.submatrix s t).det}

p2m_export "CoherentBaseChange.TwoTermComplex" "minors"

private theorem _root_.CoherentBaseChange.TwoTermComplex.det_map_submatrix (r : ℕ) (𝔭 : PrimeSpectrum R)
    (s : Fin (r + 1) → Module.Free.ChooseBasisIndex R G.C1)
    (t : Fin (r + 1) → Module.Free.ChooseBasisIndex R G.C0) :
    ((G.Md.map (algebraMap R (κ 𝔭))).submatrix s t).det
      = algebraMap R (κ 𝔭) ((G.Md.submatrix s t).det) := by
  have hsub : (G.Md.map (algebraMap R (κ 𝔭))).submatrix s t
      = (algebraMap R (κ 𝔭)).mapMatrix (G.Md.submatrix s t) := rfl
  rw [hsub, ← RingHom.map_det]

p2m_export "CoherentBaseChange.TwoTermComplex" "det_map_submatrix"

private theorem _root_.CoherentBaseChange.TwoTermComplex.minors_subset_of_fibreRank_le (r : ℕ) (𝔭 : PrimeSpectrum R)
    (hrk : G.fibreRank 𝔭 ≤ r) :
    G.minors r ⊆ (𝔭.asIdeal : Set R) := by
  classical
  rintro x ⟨s, t, rfl⟩
  rw [G.fibreRank_eq_rank_map] at hrk
  have hsub_rank : ((G.Md.map (algebraMap R (κ 𝔭))).submatrix s t).rank ≤ r :=
    (Matrix.rank_submatrix_le _ s t).trans hrk
  have hdet : ((G.Md.map (algebraMap R (κ 𝔭))).submatrix s t).det = 0 := by
    by_contra hne
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hne)
    have hrank_eq := Matrix.rank_of_isUnit _ hunit
    rw [Fintype.card_fin] at hrank_eq
    omega
  rw [G.det_map_submatrix] at hdet
  show (G.Md.submatrix s t).det ∈ 𝔭.asIdeal
  have hker : (G.Md.submatrix s t).det ∈ RingHom.ker (algebraMap R (κ 𝔭)) := hdet
  rwa [Ideal.ker_algebraMap_residueField] at hker

p2m_export "CoherentBaseChange.TwoTermComplex" "minors_subset_of_fibreRank_le"

private theorem _root_.CoherentBaseChange.TwoTermComplex.setOf_fibreRank_le_eq_zeroLocus (r : ℕ) :
    {𝔭 : PrimeSpectrum R | G.fibreRank 𝔭 ≤ r} = PrimeSpectrum.zeroLocus (G.minors r) := by
  refine Set.Subset.antisymm (fun 𝔭 hrk => ?_) (fun 𝔭 h𝔭 => ?_)
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (G.minors_subset_of_fibreRank_le r 𝔭 hrk)
  · rw [PrimeSpectrum.mem_zeroLocus] at h𝔭
    show G.fibreRank 𝔭 ≤ r
    rw [G.fibreRank_eq_rank_map]
    refine rank_le_of_det_submatrix_eq_zero _ r (fun s t => ?_)
    rw [G.det_map_submatrix]
    have hmem : (G.Md.submatrix s t).det ∈ 𝔭.asIdeal := h𝔭 ⟨s, t, rfl⟩
    show (G.Md.submatrix s t).det ∈ RingHom.ker (algebraMap R (κ 𝔭))
    rwa [Ideal.ker_algebraMap_residueField]

p2m_export "CoherentBaseChange.TwoTermComplex" "setOf_fibreRank_le_eq_zeroLocus"

private theorem _root_.CoherentBaseChange.TwoTermComplex.isClosed_fibreRank_le (r : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | G.fibreRank 𝔭 ≤ r} := by
  rw [G.setOf_fibreRank_le_eq_zeroLocus r]
  exact PrimeSpectrum.isClosed_zeroLocus (G.minors r)

p2m_export "CoherentBaseChange.TwoTermComplex" "isClosed_fibreRank_le"

private theorem _root_.CoherentBaseChange.TwoTermComplex.isClosed_le_fibreH0 (n : ℕ) :
    IsClosed {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭} := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (PrimeSpectrum R) := inferInstance
    rw [Set.eq_empty_of_isEmpty {𝔭 : PrimeSpectrum R | n ≤ G.fibreH0 𝔭}]
    exact isClosed_empty
  · haveI : StrongRankCondition R := commRing_strongRankCondition R
    rw [G.setOf_le_fibreH0_eq n]
    exact isClosed_add_le_const G.isClosed_fibreRank_le n (Module.finrank R G.C0)

p2m_export "CoherentBaseChange.TwoTermComplex" "isClosed_le_fibreH0"
end CoherentBaseChange.TwoTermComplex

namespace CoherentBaseChange
p2m_export "CoherentBaseChange" "FibreH0Family TwoTermComplex"
namespace FibreH0Family
p2m_export "CoherentBaseChange.FibreH0Family" "G hglue h0"
p2m_open "CoherentBaseChange.FibreH0Family CoherentBaseChange"

variable {T : Scheme.{u}} (F : FibreH0Family T)

private theorem _root_.CoherentBaseChange.FibreH0Family.isClosed_le_h0_perAffine (U : T.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    IsClosed {t : U | n ≤ F.h0 t} := by
  have hset : {t : U | n ≤ F.h0 t}
      = (hU.primeIdealOf) ⁻¹' {𝔭 | n ≤ (F.G U hU).fibreH0 𝔭} := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_preimage, F.hglue U hU t]
  rw [hset]
  exact ((F.G U hU).isClosed_le_fibreH0 n).preimage hU.isoSpec.hom.continuous

p2m_export "CoherentBaseChange.FibreH0Family" "isClosed_le_h0_perAffine"

private theorem _root_.CoherentBaseChange.FibreH0Family.isClosed_le_h0_impl (n : ℕ) :
    IsClosed {t : T | n ≤ F.h0 t} := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top T)]
  intro U
  exact F.isClosed_le_h0_perAffine U.1 U.2 n

p2m_export "CoherentBaseChange.FibreH0Family" "isClosed_le_h0_impl"
end CoherentBaseChange.FibreH0Family

theorem solution {T : Scheme.{u}}
    (F : FibreH0Family T) (n : ℕ) :
    IsClosed {t : T | n ≤ F.h0 t} :=
  F.isClosed_le_h0_impl n

end
end S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0
end P2MW
export P2MW.S_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0 (solution)
