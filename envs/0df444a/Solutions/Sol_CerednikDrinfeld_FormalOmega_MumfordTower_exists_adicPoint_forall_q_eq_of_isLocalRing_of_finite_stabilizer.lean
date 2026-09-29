-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a91aa81c-a025-53cb-bcf9-f2db6e388917

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_edgeNondegAt_pullback_act_inv
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "gl_smul_mk scalar_eq_scalarGL pgl_mk_smul tree BruhatTits.gl_smul_mk BruhatTits.scalar_eq_scalarGL BruhatTits.pgl_mk_smul FormalOmega.MumfordTower FormalOmega.DeligneDatum FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "MumfordTower modPow modPowTransition AdicPoint DeligneDatum.pullback DeligneDatum.isPullback_pullback DeligneDatum.map Omega DeligneDatum.map_pullback Omega.action latticeBaseChange FullLattice.act DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback chartERing Omega.action_scalarGL DeligneDatum.edgeNondegAt_pullback_act_inv DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt"
namespace C4Aux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section Pullback

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem isPullback_iff (g : GL (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) π B g d d' ↔ d' = DeligneDatum.pullback π B g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g d

theorem act_eq (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    (Omega.action K π).act B g d = DeligneDatum.pullback π B g⁻¹ d := rfl

theorem pullback_inv_eq_of_mk_eq (g g' : GL (Fin 2) K) (h : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk g')
    (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g'⁻¹ d = DeligneDatum.pullback π B g⁻¹ d := by
  have h' : (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))) g = (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))) g' := h
  rw [QuotientGroup.mk'_eq_mk'] at h'
  obtain ⟨z, hz, rfl⟩ := h'
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, rfl⟩ := hz
  rw [BruhatTits.scalar_eq_scalarGL, ← act_eq, ← act_eq, (Omega.action K π).act_mul B g (scalarGL c) d]
  change (Omega.action K π).act B g ((Omega.action K π).act B (scalarGL c) d) = _
  rw [Omega.action_scalarGL π B c d]

end Pullback

section ZeroRing

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem subsingleton_deligneDatum [Subsingleton B] : Subsingleton (DeligneDatum (K := K) π B) := by
  refine ⟨fun d d' => DeligneDatum.ext' (funext fun M => ?_)⟩
  haveI : Subsingleton (latticeBaseChange 𝒪 K B M) := Module.subsingleton B _
  exact Subsingleton.elim _ _

noncomputable def trivialDatum [Subsingleton B] : DeligneDatum (K := K) π B where
  line M := ⊥
  invertible M := by
    haveI : Subsingleton (latticeBaseChange 𝒪 K B M) := Module.subsingleton B _
    haveI : Subsingleton (latticeBaseChange 𝒪 K B M ⧸ (⊥ : Submodule B (latticeBaseChange 𝒪 K B M))) :=
      Module.subsingleton B _
    exact Module.Invertible.congr (LinearEquiv.ofSubsingleton B (latticeBaseChange 𝒪 K B M ⧸ (⊥ : Submodule B _)))
  mono h := by rw [Submodule.map_bot]
  homothety c M := by rw [Submodule.map_bot]
  nondeg 𝔭 h𝔭 := by
    exfalso
    apply h𝔭.ne_top
    haveI : Subsingleton (Ideal B) := by
      haveI : Subsingleton B := inferInstance
      exact Unique.instSubsingleton
    exact Subsingleton.elim _ _

end ZeroRing

section Lift

variable {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)

theorem exists_q_eq_of_isLocalRing (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (z : Spec (CommRingCat.of B) ⟶ DM.Z n)
    (hz : z ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) :
    ∃ P : (Omega K₀ π).obj B, DM.q n B hB P = z := by
  classical
  let A : Type := (chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}
  have hA : (algebraMap 𝒪 A π) ^ (n + 1) = 0 := by
    have e : algebraMap 𝒪 A π =
        Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) π) := rfl
    rw [e, ← RingHom.map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  obtain ⟨h, d, P, hchart, hpb, hx⟩ := DM.cover n hA (z.base (IsLocalRing.closedPoint B))
  haveI : IsOpenImmersion (DM.q n A hA P) := DM.chart_isOpenImmersion h n hA d P hchart hpb
  have hrange : Set.range z.base ⊆ Set.range (DM.q n A hA P).base := by
    have hopen : IsOpen (z.base ⁻¹' Set.range (DM.q n A hA P).base) :=
      ((DM.q n A hA P).isOpenEmbedding.isOpen_range).preimage z.continuous
    let U : TopologicalSpace.Opens (PrimeSpectrum B) := ⟨z.base ⁻¹' Set.range (DM.q n A hA P).base, hopen⟩
    have hU : IsLocalRing.closedPoint B ∈ U := hx
    rw [IsLocalRing.closed_point_mem_iff] at hU
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ U := by rw [hU]; trivial
    exact hy
  let z' : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := IsOpenImmersion.lift (DM.q n A hA P) z hrange
  have hz' : z' ≫ DM.q n A hA P = z := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective z'
  have hcomp : φ₀.hom.comp (algebraMap 𝒪 A) = algebraMap 𝒪 B := by
    have e : Spec.map (CommRingCat.ofHom (algebraMap 𝒪 A) ≫ φ₀) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)) := by
      rw [Spec.map_comp, hφ₀, ← hz, ← DM.q_over n A hA P, ← Category.assoc, ← Category.assoc, hz']
      rfl
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rwa [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at this
  let φ : A →ₐ[𝒪] B :=
    { toRingHom := φ₀.hom
      commutes' := fun a => by
        have := congrArg (fun f : 𝒪 →+* B => f a) hcomp
        exact this }
  refine ⟨(Omega K₀ π).map φ P, ?_⟩
  rw [DM.q_natural n A B hA hB φ P]
  have : Spec.map (CommRingCat.ofHom φ.toRingHom) = z' := by
    rw [← hφ₀]; rfl
  rw [this, hz']

theorem mono_zt (n : ℕ) : Mono (DM.zt n) := by
  have hle : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  exact IsPullback.mono_fst_of_mono (DM.zt_isPullback n) inferInstance

end Lift

theorem exists_forall_mem_of_antitone {α : Type} (T : ℕ → Set α) (h0 : (T 0).Finite)
    (hne : ∀ n, (T n).Nonempty) (hmono : ∀ n, T (n + 1) ⊆ T n) : ∃ a, ∀ n, a ∈ T n := by
  classical
  have hanti : ∀ m n, m ≤ n → T n ⊆ T m := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact (hmono _).trans ih
  have hfin : ∀ n, (T n).Finite := fun n => h0.subset (hanti 0 n (Nat.zero_le n))
  let f : ℕ → ℕ := fun n => (T n).ncard
  let n₀ := Function.argmin f
  obtain ⟨a, ha⟩ := hne n₀
  refine ⟨a, fun n => ?_⟩
  rcases le_total n n₀ with hle | hle
  · exact hanti n n₀ hle ha
  · have hsub : T n ⊆ T n₀ := hanti n₀ n hle
    have hcard : (T n₀).ncard ≤ (T n).ncard := Function.argmin_le f n
    have heq : T n = T n₀ := Set.eq_of_subset_of_ncard_le hsub hcard (hfin n₀)
    rw [heq]; exact ha

end CerednikDrinfeld.FormalOmega.C4Aux

open CerednikDrinfeld.FormalOmega.C4Aux

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))

    (hNfin : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ N ∧ g • v = v})
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra 𝒪 R]
    (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0) :
    (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ DM.Z n,
      (∀ n : ℕ, η n ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ DM.zt n) →
      ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = DM.q n (modPow π R n) (hmod n) (x.pt n)) ∧
    (∀ x x' : AdicPoint K₀ π R,
      (∀ n : ℕ, DM.q n (modPow π R n) (hmod n) (x.pt n) = DM.q n (modPow π R n) (hmod n) (x'.pt n)) ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
        ∀ n : ℕ, DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n)) := by
  classical
  haveI := hdvr

  have hii_easy : ∀ x x' : AdicPoint K₀ π R, (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
        ∀ n : ℕ, DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n)) →
      ∀ n : ℕ, DM.q n (modPow π R n) (hmod n) (x.pt n) = DM.q n (modPow π R n) (hmod n) (x'.pt n) := by
    rintro x x' ⟨g, hg, hgx⟩ n
    exact (DM.q_inv n (modPow π R n) (hmod n) g hg (x.pt n) (x'.pt n) (hgx n)).symm
  by_cases hunit : IsUnit (algebraMap 𝒪 R π)
  ·
    have hsub : ∀ n, Subsingleton (modPow π R n) := fun n =>
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span rfl) (hunit.pow (n + 1)))
    have hempty : ∀ n, IsEmpty ↥(Spec (CommRingCat.of (modPow π R n))) := fun n => by
      haveI := hsub n
      change IsEmpty (PrimeSpectrum (modPow π R n))
      infer_instance
    have hext : ∀ n (T : Scheme) (a b : Spec (CommRingCat.of (modPow π R n)) ⟶ T), a = b := fun n T a b => by
      haveI := hempty n
      exact Limits.IsInitial.hom_ext isInitialOfIsEmpty a b
    refine ⟨fun η _ _ => ?_, fun x x' => ⟨fun _ => ?_, hii_easy x x'⟩⟩
    · haveI := hsub
      refine ⟨⟨fun n => trivialDatum π (modPow π R n), fun n => ?_⟩, fun n => hext n _ _ _⟩
      haveI := subsingleton_deligneDatum (K := K₀) π (modPow π R n)
      exact Subsingleton.elim _ _
    · refine ⟨1, by rw [map_one]; exact N.one_mem, fun n => ?_⟩
      haveI := hsub n
      haveI := subsingleton_deligneDatum (K := K₀) π (modPow π R n)
      rw [isPullback_iff]
      exact Subsingleton.elim _ _

  have hmem : algebraMap 𝒪 R π ∈ IsLocalRing.maximalIdeal R := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hne_top : ∀ n, Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} ≠ (⊤ : Ideal R) := fun n htop => by
    have hle : Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} ≤ IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]; rintro _ rfl
      exact Ideal.pow_mem_of_mem _ hmem _ (Nat.succ_pos n)
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)
  haveI hlocal : ∀ n, IsLocalRing (modPow π R n) := fun n => by
    haveI : Nontrivial (modPow π R n) := Ideal.Quotient.nontrivial_iff.mpr (hne_top n)
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : ∀ n, Mono (DM.zt n) := mono_zt 𝒪 π K₀ g₁ N DM
  refine ⟨fun η hηb hηt => ?_, fun x x' => ⟨fun hq => ?_, hii_easy x x'⟩⟩
  ·
    let L : ℕ → Type := fun n => {P : (Omega K₀ π).obj (modPow π R n) // η n = DM.q n (modPow π R n) (hmod n) P}
    have base : Nonempty (L 0) := by
      obtain ⟨P, hP⟩ := exists_q_eq_of_isLocalRing 𝒪 π K₀ g₁ N DM 0 (modPow π R 0) (hmod 0) (η 0) (hηb 0)
      exact ⟨⟨P, hP.symm⟩⟩
    have step : ∀ n (s : L n), ∃ s' : L (n + 1), DeligneDatum.map π (modPowTransition π R n) s'.1 = s.1 := by
      rintro n ⟨P, hP⟩
      obtain ⟨y, hy⟩ := exists_q_eq_of_isLocalRing 𝒪 π K₀ g₁ N DM (n + 1) (modPow π R (n + 1)) (hmod (n + 1))
        (η (n + 1)) (hηb (n + 1))
      let y' : (Omega K₀ π).obj (modPow π R n) := (Omega K₀ π).map (modPowTransition π R n) y
      have h' : (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1 + 1) = 0 := by
        rw [pow_succ, hmod n, zero_mul]
      have h1 : DM.q (n + 1) (modPow π R n) h' y' =
          Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ DM.q (n + 1) (modPow π R (n + 1)) (hmod (n + 1)) y :=
        DM.q_natural (n + 1) (modPow π R (n + 1)) (modPow π R n) (hmod (n + 1)) h' (modPowTransition π R n) y
      have h2 : DM.q (n + 1) (modPow π R n) h' y' = DM.q n (modPow π R n) (hmod n) y' ≫ DM.zt n :=
        DM.q_zt n (modPow π R n) (hmod n) h' y'
      have h3 : DM.q n (modPow π R n) (hmod n) y' = DM.q n (modPow π R n) (hmod n) P := by
        rw [← cancel_mono (DM.zt n), ← h2, h1, hy, hηt n, hP]
      obtain ⟨g, hg, hpb⟩ := (DM.q_localFib n (modPow π R n) (hmod n) y' P).mp h3
      refine ⟨⟨DeligneDatum.pullback π (modPow π R (n + 1)) g⁻¹ y, ?_⟩, ?_⟩
      · rw [DM.q_inv (n + 1) (modPow π R (n + 1)) (hmod (n + 1)) g hg y _
          (DeligneDatum.isPullback_pullback π _ g⁻¹ y), hy]
      · change DeligneDatum.map π (modPowTransition π R n) (DeligneDatum.pullback π (modPow π R (n + 1)) g⁻¹ y) = P
        rw [DeligneDatum.map_pullback]
        exact ((isPullback_iff π _ g⁻¹ y' P).mp hpb).symm
    choose stepF hstepF using step
    let F : ∀ n, L n := fun n => Nat.rec (Classical.choice base) (fun n s => stepF n s) n
    refine ⟨⟨fun n => (F n).1, fun n => hstepF n (F n)⟩, fun n => (F n).2⟩
  ·
    let T : ℕ → Set (PGL(2, K₀)) := fun n =>
      {q | q ∈ N ∧ ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g = q ∧
        DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n)}
    have hT_rep : ∀ n (g : Matrix.GeneralLinearGroup (Fin 2) K₀), Matrix.ProjGenLinGroup.mk g ∈ T n ↔
        Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n) := by
      intro n g
      constructor
      · rintro ⟨hN, g', hg', hpb⟩
        refine ⟨hN, ?_⟩
        rw [isPullback_iff] at hpb ⊢
        rw [hpb, pullback_inv_eq_of_mk_eq π _ g g' hg'.symm]
      · rintro ⟨hN, hpb⟩
        exact ⟨hN, g, rfl, hpb⟩
    have hTne : ∀ n, (T n).Nonempty := fun n => by
      obtain ⟨g, hg, hpb⟩ := (DM.q_localFib n (modPow π R n) (hmod n) (x.pt n) (x'.pt n)).mp (hq n)
      exact ⟨Matrix.ProjGenLinGroup.mk g, (hT_rep n g).mpr ⟨hg, hpb⟩⟩
    have hTmono : ∀ n, T (n + 1) ⊆ T n := by
      rintro n q ⟨hN, g, rfl, hpb⟩
      refine ⟨hN, g, rfl, ?_⟩
      rw [isPullback_iff] at hpb ⊢
      rw [← x'.compat n, ← x.compat n, hpb, DeligneDatum.map_pullback]
    have hT0 : (T 0).Finite := by

      have hfinP : ∀ a b : Vertex 𝒪 K₀, Set.Finite {q : PGL(2, K₀) | q ∈ N ∧ q • a = b} := by
        intro a b
        by_cases h : ∃ q₀ : PGL(2, K₀), q₀ ∈ N ∧ q₀ • a = b
        · obtain ⟨q₀, hq₀N, hq₀⟩ := h
          refine ((hNfin a).image (fun q => q₀ * q)).subset ?_
          rintro q ⟨hqN, hqa⟩
          refine ⟨q₀⁻¹ * q, ⟨N.mul_mem (N.inv_mem hq₀N) hqN, ?_⟩, by simp⟩
          rw [mul_smul, hqa, inv_smul_eq_iff, hq₀]
        · refine Set.Finite.subset Set.finite_empty ?_
          rintro q ⟨hqN, hqa⟩
          exact h ⟨q, hqN, hqa⟩

      let B₀ : Type := modPow π R 0
      let 𝔪 : Ideal B₀ := IsLocalRing.maximalIdeal B₀
      haveI h𝔪 : 𝔪.IsPrime := (IsLocalRing.maximalIdeal.isMaximal B₀).isPrime
      have hπ𝔪 : algebraMap 𝒪 B₀ π ∈ 𝔪 := by
        have h0 : algebraMap 𝒪 B₀ π = 0 := by simpa [pow_one] using hmod 0
        rw [h0]; exact zero_mem _
      obtain ⟨M', M, hM⟩ := (x.pt 0).exists_edgeNondegAt π 𝔪 h𝔪
      obtain ⟨L', L, hL⟩ := (x'.pt 0).exists_edgeNondegAt π 𝔪 h𝔪
      let vx : FullLattice 𝒪 K₀ → Vertex 𝒪 K₀ := fun X => Vertex.mk 𝒪 K₀ X.1 X.2
      refine ((((hfinP (vx M') (vx L')).union (hfinP (vx M') (vx L))).union (hfinP (vx M) (vx L'))).union
        (hfinP (vx M) (vx L))).subset ?_
      rintro q ⟨hN, g, rfl, hpb⟩
      have hd' : x'.pt 0 = DeligneDatum.pullback π B₀ g⁻¹ (x.pt 0) := (isPullback_iff π B₀ g⁻¹ _ _).mp hpb
      have hE : (x'.pt 0).EdgeNondegAt π 𝔪 (FullLattice.act g M') (FullLattice.act g M) := by
        have := CerednikDrinfeld.FormalOmega.DeligneDatum.edgeNondegAt_pullback_act_inv π (x.pt 0) g⁻¹ 𝔪 M' M hM
        rwa [inv_inv, ← hd'] at this
      obtain ⟨c, X, Y, hX, hY, hXY⟩ :=
        CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_of_edgeNondegAt_of_edgeNondegAt
          hπ (x'.pt 0) 𝔪 hπ𝔪 (FullLattice.act g M') (FullLattice.act g M) L' L hE hL
      have hv : ∀ X₀ : FullLattice 𝒪 K₀, X = FullLattice.act g X₀ → Matrix.ProjGenLinGroup.mk g • vx X₀ = vx Y := by
        rintro X₀ rfl
        rw [BruhatTits.pgl_mk_smul, BruhatTits.gl_smul_mk, Vertex.mk_eq_mk_iff]
        exact ⟨c, hXY⟩
      rcases hX with hX | hX <;> rcases hY with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl ⟨hN, hv M' hX⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hN, hv M' hX⟩))
      · exact Or.inl (Or.inr ⟨hN, hv M hX⟩)
      · exact Or.inr ⟨hN, hv M hX⟩
    obtain ⟨q, hqT⟩ := exists_forall_mem_of_antitone T hT0 hTne hTmono
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q
    exact ⟨g, ((hT_rep 0 g).mp (hqT 0)).1, fun n => ((hT_rep n g).mp (hqT n)).2⟩

end S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer (solution)
