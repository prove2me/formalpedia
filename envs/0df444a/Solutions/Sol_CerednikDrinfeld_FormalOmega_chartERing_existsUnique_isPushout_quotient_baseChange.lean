-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_quotient_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e0930cf4-13d7-5b1a-8296-96b51543b5c2

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace G5Body

theorem span_pow_le_comap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) (k : ℕ) :
    Ideal.span {a ^ k} ≤ (Ideal.span {(f a) ^ k}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  exact Ideal.subset_span rfl

abbrev truncJ (R : Type) [CommRing R] (π : R) (n : ℕ) : Ideal R := Ideal.span {π ^ (n + 1)}

abbrev truncI (R : Type) [CommRing R] (π : R) (q n : ℕ) : Ideal (chartERing R π q) :=
  Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}

def toSPoint (R : Type) [CommRing R] (π : R) (q : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (T : Type) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (x : (chartE R π q).obj T) : (chartE S (algebraMap R S π) q).obj T :=
  ⟨x.1, by
    obtain ⟨h₁, h₂, h₃⟩ := x.2
    refine ⟨?_, h₂, h₃⟩
    rw [h₁, IsScalarTower.algebraMap_apply R S T]⟩

theorem algHom_ext (R : Type) [CommRing R] (π : R) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (f g : chartERing R π q →ₐ[R] B) (hξ : f (chartERing.ξ R π q) = g (chartERing.ξ R π q))
    (hη : f (chartERing.η R π q) = g (chartERing.η R π q)) : f = g :=
  (chartERing.corepEquiv R π q B).injective (Subtype.ext (Prod.ext hξ hη))

theorem ringHom_quot_ext (R : Type) [CommRing R] (π : R) (q : ℕ) (I : Ideal (chartERing R π q))
    {B : Type} [CommRing B] [Algebra R B] (f g : chartERing R π q ⧸ I →+* B)
    (hf : ∀ r : R, f (Ideal.Quotient.mk I (algebraMap R (chartERing R π q) r)) = algebraMap R B r)
    (hg : ∀ r : R, g (Ideal.Quotient.mk I (algebraMap R (chartERing R π q) r)) = algebraMap R B r)
    (hξ : f (Ideal.Quotient.mk I (chartERing.ξ R π q)) = g (Ideal.Quotient.mk I (chartERing.ξ R π q)))
    (hη : f (Ideal.Quotient.mk I (chartERing.η R π q)) = g (Ideal.Quotient.mk I (chartERing.η R π q))) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  let f' : chartERing R π q →ₐ[R] B := { toRingHom := f.comp (Ideal.Quotient.mk I), commutes' := fun r => hf r }
  let g' : chartERing R π q →ₐ[R] B := { toRingHom := g.comp (Ideal.Quotient.mk I), commutes' := fun r => hg r }
  exact congrArg AlgHom.toRingHom (algHom_ext R π q f' g' hξ hη)

end G5Body

open G5Body in
theorem solution
    (R : Type) [CommRing R] (π : R) (q n : ℕ) (S : Type) [CommRing S] [Algebra R S] :
    ∃ φ : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
        (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
      φ.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
        (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
          (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ∧
      φ (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) ∧
      φ (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) ∧
      IsPushout
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)}))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            R ⧸ Ideal.span {π ^ (n + 1)} →+* _))
        (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
            (algebraMap S (chartERing S (algebraMap R S π) q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _))
        (CommRingCat.ofHom φ) ∧
      ∀ φ' : (chartERing R π q ⧸ Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) →+*
          (chartERing S (algebraMap R S π) q ⧸ Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)}),
        φ'.comp (Ideal.quotientMap (Ideal.span {(algebraMap R (chartERing R π q) π) ^ (n + 1)}) (algebraMap R (chartERing R π q))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
              R ⧸ Ideal.span {π ^ (n + 1)} →+* _) =
          (Ideal.quotientMap (Ideal.span {(algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)})
              (algebraMap S (chartERing S (algebraMap R S π) q))
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
                S ⧸ Ideal.span {(algebraMap R S π) ^ (n + 1)} →+* _).comp
            (Ideal.quotientMap (Ideal.span {(algebraMap R S π) ^ (n + 1)}) (algebraMap R S)
              (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) →
        φ' (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) →
        φ' (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) → φ' = φ := by
  classical

  letI algRAS : Algebra R (chartERing S (algebraMap R S π) q) :=
    ((algebraMap S (chartERing S (algebraMap R S π) q)).comp (algebraMap R S)).toAlgebra
  haveI istRS : IsScalarTower R S (chartERing S (algebraMap R S π) q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let pt : (chartE R π q).obj (chartERing S (algebraMap R S π) q) :=
    ⟨(chartERing.ξ S (algebraMap R S π) q, chartERing.η S (algebraMap R S π) q), by
      refine ⟨?_, (chartERing.point S (algebraMap R S π) q).2.2.1, (chartERing.point S (algebraMap R S π) q).2.2.2⟩
      rw [chartERing.ξ_mul_η]
      rfl⟩
  let φa : chartERing R π q →ₐ[R] chartERing S (algebraMap R S π) q := chartERing.lift pt
  have hφξ : φa (chartERing.ξ R π q) = chartERing.ξ S (algebraMap R S π) q := chartERing.lift_ξ pt
  have hφη : φa (chartERing.η R π q) = chartERing.η S (algebraMap R S π) q := chartERing.lift_η pt
  have hφalg : ∀ r : R, φa (algebraMap R (chartERing R π q) r) =
      algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S r) := fun r => φa.commutes r

  have hle : truncI R π q n ≤ (truncI S (algebraMap R S π) q n).comap φa.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    show φa (algebraMap R (chartERing R π q) π) ^ (n + 1) ∈ truncI S (algebraMap R S π) q n
    rw [hφalg]
    exact Ideal.subset_span rfl
  let φ : (chartERing R π q ⧸ truncI R π q n) →+* (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) :=
    Ideal.quotientMap (truncI S (algebraMap R S π) q n) φa.toRingHom hle
  have hφmk : ∀ a : chartERing R π q, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φa a) := fun a => rfl

  let iR : (R ⧸ truncJ R π n) →+* (chartERing R π q ⧸ truncI R π q n) :=
    Ideal.quotientMap (truncI R π q n) (algebraMap R (chartERing R π q)) (span_pow_le_comap _ _ _)
  let iS : (S ⧸ truncJ S (algebraMap R S π) n) →+* (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) :=
    Ideal.quotientMap (truncI S (algebraMap R S π) q n) (algebraMap S (chartERing S (algebraMap R S π) q))
      (span_pow_le_comap _ _ _)
  let f : (R ⧸ truncJ R π n) →+* (S ⧸ truncJ S (algebraMap R S π) n) :=
    Ideal.quotientMap (truncJ S (algebraMap R S π) n) (algebraMap R S) (span_pow_le_comap _ _ _)
  have hcomp : φ.comp iR = iS.comp f := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun r => ?_
    show Ideal.Quotient.mk (truncI S (algebraMap R S π) q n) (φa (algebraMap R (chartERing R π q) r)) =
      Ideal.Quotient.mk (truncI S (algebraMap R S π) q n) (algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S r))
    rw [hφalg]
  have hφ2 : φ (Ideal.Quotient.mk _ (chartERing.ξ R π q)) = Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q) := by
    rw [hφmk, hφξ]
  have hφ3 : φ (Ideal.Quotient.mk _ (chartERing.η R π q)) = Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q) := by
    rw [hφmk, hφη]
  refine ⟨φ, hcomp, hφ2, hφ3, ?_, ?_⟩
  ·
    letI aRnSn : Algebra (R ⧸ truncJ R π n) (S ⧸ truncJ S (algebraMap R S π) n) := f.toAlgebra
    letI aRnAn : Algebra (R ⧸ truncJ R π n) (chartERing R π q ⧸ truncI R π q n) := iR.toAlgebra
    letI aSnBn : Algebra (S ⧸ truncJ S (algebraMap R S π) n)
        (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) := iS.toAlgebra
    letI aRnBn : Algebra (R ⧸ truncJ R π n)
        (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) := (iS.comp f).toAlgebra
    letI aAnBn : Algebra (chartERing R π q ⧸ truncI R π q n)
        (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) := φ.toAlgebra
    haveI ist1 : IsScalarTower (R ⧸ truncJ R π n) (S ⧸ truncJ S (algebraMap R S π) n)
        (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI ist2 : IsScalarTower (R ⧸ truncJ R π n) (chartERing R π q ⧸ truncI R π q n)
        (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) :=
      IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hcomp x).symm)
    haveI hP : Algebra.IsPushout (R ⧸ truncJ R π n) (chartERing R π q ⧸ truncI R π q n)
        (S ⧸ truncJ S (algebraMap R S π) n) (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) := by
      refine Algebra.isPushout_of_forall_existsUnique_algHom_comp_eq (fun T _ _ g hg => ?_)

      letI aST : Algebra S T :=
        ((algebraMap (S ⧸ truncJ S (algebraMap R S π) n) T).comp (Ideal.Quotient.mk (truncJ S (algebraMap R S π) n))).toAlgebra
      letI aRT : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
      haveI istRST : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hπT : (algebraMap S T (algebraMap R S π)) ^ (n + 1) = 0 := by
        rw [← map_pow]
        show algebraMap (S ⧸ truncJ S (algebraMap R S π) n) T
            (Ideal.Quotient.mk (truncJ S (algebraMap R S π) n) ((algebraMap R S π) ^ (n + 1))) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]

      have hgalg : ∀ r : R, g (Ideal.Quotient.mk (truncI R π q n) (algebraMap R (chartERing R π q) r)) = algebraMap R T r :=
        fun r => RingHom.congr_fun hg (Ideal.Quotient.mk (truncJ R π n) r)
      let ga : chartERing R π q →ₐ[R] T :=
        { toRingHom := g.comp (Ideal.Quotient.mk (truncI R π q n)), commutes' := fun r => hgalg r }
      let x : (chartE R π q).obj T := chartERing.corepEquiv R π q T ga
      let k₀ : chartERing S (algebraMap R S π) q →ₐ[S] T := chartERing.lift (toSPoint R π q S T x)
      have hk₀ξ : k₀ (chartERing.ξ S (algebraMap R S π) q) = g (Ideal.Quotient.mk _ (chartERing.ξ R π q)) :=
        chartERing.lift_ξ _
      have hk₀η : k₀ (chartERing.η S (algebraMap R S π) q) = g (Ideal.Quotient.mk _ (chartERing.η R π q)) :=
        chartERing.lift_η _
      have hk₀I : ∀ a ∈ truncI S (algebraMap R S π) q n, k₀.toRingHom a = 0 := fun a ha => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        show k₀ (c * (algebraMap S (chartERing S (algebraMap R S π) q) (algebraMap R S π)) ^ (n + 1)) = 0
        rw [map_mul, map_pow, AlgHom.commutes, hπT, mul_zero]
      let k : (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n) →ₐ[S ⧸ truncJ S (algebraMap R S π) n] T :=
        { toRingHom := Ideal.Quotient.lift (truncI S (algebraMap R S π) q n) k₀.toRingHom hk₀I
          commutes' := fun s => by
            obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
            exact k₀.commutes s }
      have hkmk : ∀ b : chartERing S (algebraMap R S π) q, k (Ideal.Quotient.mk _ b) = k₀ b := fun b => rfl
      refine ⟨k, ?_, ?_⟩
      ·
        show k.toRingHom.comp φ = g
        apply ringHom_quot_ext R π q (truncI R π q n)
        · intro r
          show k (φ (Ideal.Quotient.mk _ (algebraMap R (chartERing R π q) r))) = algebraMap R T r
          rw [hφmk, hkmk, hφalg, AlgHom.commutes]
          rfl
        · exact hgalg
        · show k (φ (Ideal.Quotient.mk _ (chartERing.ξ R π q))) = g (Ideal.Quotient.mk _ (chartERing.ξ R π q))
          rw [hφ2, hkmk, hk₀ξ]
        · show k (φ (Ideal.Quotient.mk _ (chartERing.η R π q))) = g (Ideal.Quotient.mk _ (chartERing.η R π q))
          rw [hφ3, hkmk, hk₀η]
      ·
        intro k' hk'
        apply AlgHom.coe_ringHom_injective
        apply ringHom_quot_ext S (algebraMap R S π) q (truncI S (algebraMap R S π) q n)
        · intro s
          exact k'.commutes (Ideal.Quotient.mk _ s)
        · intro s
          exact k₀.commutes s
        · show k' (Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q)) = k (Ideal.Quotient.mk _ (chartERing.ξ S (algebraMap R S π) q))
          rw [hkmk, hk₀ξ, ← hφ2]
          exact RingHom.congr_fun hk' (Ideal.Quotient.mk _ (chartERing.ξ R π q))
        · show k' (Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q)) = k (Ideal.Quotient.mk _ (chartERing.η S (algebraMap R S π) q))
          rw [hkmk, hk₀η, ← hφ3]
          exact RingHom.congr_fun hk' (Ideal.Quotient.mk _ (chartERing.η R π q))
    haveI := hP.symm
    exact CommRingCat.isPushout_of_isPushout (R ⧸ truncJ R π n) (S ⧸ truncJ S (algebraMap R S π) n)
      (chartERing R π q ⧸ truncI R π q n) (chartERing S (algebraMap R S π) q ⧸ truncI S (algebraMap R S π) q n)
  ·
    intro φ' h1 h2 h3
    apply ringHom_quot_ext R π q (truncI R π q n) φ' φ
    · intro r
      exact RingHom.congr_fun h1 (Ideal.Quotient.mk _ r)
    · intro r
      show Ideal.Quotient.mk _ (φa (algebraMap R (chartERing R π q) r)) = _
      rw [hφalg]
      rfl
    · rw [h2, hφ2]
    · rw [h3, hφ3]

end

end S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange (solution)
