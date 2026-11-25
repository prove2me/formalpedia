-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_eq_of_etale_affineSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:29:22.832573+00:00
-- url     : https://prove2.me/submissions/7711fb0b-7618-48b4-9289-9f9d34d70ade

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_eq_of_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_le_of_etale_affineSpace
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_stalk_affineSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map


section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem fromSpecStalkPoint_specializes_iff (X : Scheme.{u}) (x : X)
    (p q : PrimeSpectrum (X.presheaf.stalk x)) :
    fromSpecStalkPoint X x p ⤳ fromSpecStalkPoint X x q ↔ p ⤳ q :=
  (AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)).toIsInducing.specializes_iff
private theorem exists_fromSpecStalkPoint_eq_of_specializes (X : Scheme.{u}) (x : X) {y : X} (h : y ⤳ x) :
    ∃ p : PrimeSpectrum (X.presheaf.stalk x), fromSpecStalkPoint X x p = y := by
  have hy : y ∈ Set.range (X.fromSpecStalk x).base := by
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]; exact h
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, hp⟩
private theorem comap_comap_symm {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (I : Ideal A) : Ideal.comap (φ : A →+* B) (Ideal.comap (φ.symm : B →+* A) I) = I := by
  refine Ideal.ext fun a => ?_
  have h : (φ.symm : B →+* A) ((φ : A →+* B) a) = a := φ.symm_apply_apply a
  constructor
  · intro hmem
    have hmem' : (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ.symm : B →+* A) ((φ : A →+* B) a) ∈ I
    rw [h]
    exact hmem
private theorem comap_symm_comap {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (J : Ideal B) : Ideal.comap (φ.symm : B →+* A) (Ideal.comap (φ : A →+* B) J) = J := by
  refine Ideal.ext fun b => ?_
  have h : (φ : A →+* B) ((φ.symm : B →+* A) b) = b := φ.apply_symm_apply b
  constructor
  · intro hmem
    have hmem' : (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J := hmem
    rwa [h] at hmem'
  · intro hmem
    show (φ : A →+* B) ((φ.symm : B →+* A) b) ∈ J
    rw [h]
    exact hmem
private theorem exists_ltSeries_comap {A B : Type u} [CommRing A] [CommRing B] (φ : A ≃+* B)
    (s : LTSeries (PrimeSpectrum B)) :
    ∃ t : LTSeries (PrimeSpectrum A), t.length = s.length ∧
      t.last.asIdeal = Ideal.comap (φ : A →+* B) s.last.asIdeal := by
  have hmono : Monotone (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr h)
  have hinj : Function.Injective (PrimeSpectrum.comap (φ : A →+* B)) := by
    intro p q h
    have h' : Ideal.comap (φ : A →+* B) p.asIdeal = Ideal.comap (φ : A →+* B) q.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, ← PrimeSpectrum.comap_asIdeal, h]
    have h2 := congrArg (Ideal.comap (φ.symm : B →+* A)) h'
    rw [comap_symm_comap φ p.asIdeal, comap_symm_comap φ q.asIdeal] at h2
    exact PrimeSpectrum.ext h2
  have hstrict := hmono.strictMono_of_injective hinj
  exact ⟨⟨s.length, fun i => PrimeSpectrum.comap (φ : A →+* B) (s i), fun i => hstrict (s.step i)⟩,
    rfl, rfl⟩
private theorem comap_C_map_C {S : Type u} [CommRing S] (I : Ideal S) :
    Ideal.comap (Polynomial.C : S →+* Polynomial S) (I.map (Polynomial.C : S →+* Polynomial S))
      = I := by
  refine Ideal.ext fun a => ?_
  constructor
  · intro h
    have h2 : (Polynomial.C a) ∈ I.map (Polynomial.C : S →+* Polynomial S) := h
    have h3 := (Ideal.mem_map_C_iff).mp h2 0
    simpa using h3
  · intro h
    exact Ideal.mem_map_of_mem _ h
private theorem isMaximal_comap_C {S : Type u} [CommRing S] [IsJacobsonRing S]
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    (Ideal.comap (Polynomial.C : S →+* Polynomial S) M').IsMaximal := by
  have := hM'
  have hint : ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)).IsIntegral :=
    Polynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing M'
  have hbot : (⊥ : Ideal (Polynomial S ⧸ M')).IsMaximal := by
    let fieldQuot : Field (Polynomial S ⧸ M') := Ideal.Quotient.field M'
    exact Ideal.bot_isMaximal
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S)) hint
    (⊥ : Ideal (Polynomial S ⧸ M'))
  have hker : Ideal.comap ((Ideal.Quotient.mk M').comp (Polynomial.C : S →+* Polynomial S))
      (⊥ : Ideal (Polynomial S ⧸ M')) = Ideal.comap (Polynomial.C : S →+* Polynomial S) M' := by
    refine Ideal.ext fun a => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker]
  exact hmax
private theorem map_C_ne_of_isMaximal {S : Type u} [CommRing S] (N : Ideal S) (hN : N.IsMaximal)
    (M' : Ideal (Polynomial S)) (hM' : M'.IsMaximal) :
    N.map (Polynomial.C : S →+* Polynomial S) ≠ M' := by
  intro h
  have hX : (Polynomial.X : Polynomial S) ∉ M' := by
    rw [← h]
    intro hmem
    have h1 := (Ideal.mem_map_C_iff).mp hmem 1
    rw [Polynomial.coeff_X_one] at h1
    exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h1)
  obtain ⟨y, i, hi, hyi⟩ := hM'.exists_inv hX
  rw [← h] at hi
  have hc := (Ideal.mem_map_C_iff).mp hi 0
  have h0 : (y * Polynomial.X + i).coeff 0 = (1 : Polynomial S).coeff 0 := by rw [hyi]
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.mul_coeff_zero,
    Polynomial.coeff_X_zero, mul_zero, zero_add] at h0
  have hone : (1 : S) ∈ N := by rw [← h0]; exact hc
  exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr hone)
private theorem exists_ltSeries_of_isMaximal_mvPolynomial (k : Type u) [Field k] :
    ∀ (m : ℕ) (M : Ideal (MvPolynomial (Fin m) k)), M.IsMaximal →
      ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) k)),
        s.length = m ∧ s.last.asIdeal = M := by
  intro m
  induction m with
  | zero =>
    intro M hM
    exact ⟨RelSeries.singleton _ ⟨M, hM.isPrime⟩, rfl, rfl⟩
  | succ n ih =>
    intro M hM
    have := hM
    have hJ : IsJacobsonRing (MvPolynomial (Fin n) k) := by
      have : Algebra.FiniteType k (MvPolynomial (Fin n) k) := inferInstance
      exact isJacobsonRing_of_finiteType (A := k)
    let φ : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial (MvPolynomial (Fin n) k) :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) :=
      Ideal.comap
        (φ.symm : Polynomial (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin (n + 1)) k) M
    have hM'max : M'.IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
    let N : Ideal (MvPolynomial (Fin n) k) :=
      Ideal.comap
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) M'
    have hNmax : N.IsMaximal := isMaximal_comap_C M' hM'max
    obtain ⟨t, htlen, htlast⟩ := ih N hNmax
    have hFs : StrictMono (fun p : PrimeSpectrum (MvPolynomial (Fin n) k) =>
        (⟨p.asIdeal.map
            (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
          (Ideal.isPrime_map_C_iff_isPrime p.asIdeal).mpr p.isPrime⟩ :
          PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k)))) := by
      refine Monotone.strictMono_of_injective ?_ ?_
      · intro p q hpq
        rw [← PrimeSpectrum.asIdeal_le_asIdeal]
        exact Ideal.map_mono ((PrimeSpectrum.asIdeal_le_asIdeal p q).mpr hpq)
      · intro p q hpq
        have h' : p.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k))
            = q.asIdeal.map
              (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) :=
          congrArg PrimeSpectrum.asIdeal hpq
        refine PrimeSpectrum.ext ?_
        rw [← comap_C_map_C p.asIdeal, ← comap_C_map_C q.asIdeal, h']
    let t1 : LTSeries (PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) :=
      ⟨t.length, fun i => ⟨(t i).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)),
        (Ideal.isPrime_map_C_iff_isPrime (t i).asIdeal).mpr (t i).isPrime⟩,
        fun i => hFs (t.step i)⟩
    have ht1last : t1.last.asIdeal = N.map
        (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) := by
      show (t.last).asIdeal.map
          (Polynomial.C : MvPolynomial (Fin n) k →+* Polynomial (MvPolynomial (Fin n) k)) = _
      rw [htlast]
    have hle : t1.last.asIdeal ≤ M' := by
      rw [ht1last]
      exact Ideal.map_le_iff_le_comap.mpr le_rfl
    have hlt : t1.last <
        (⟨M', hM'max.isPrime⟩ : PrimeSpectrum (Polynomial (MvPolynomial (Fin n) k))) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hle) ?_
      intro hEq
      have hEq' : t1.last.asIdeal = M' := congrArg PrimeSpectrum.asIdeal hEq
      rw [ht1last] at hEq'
      exact map_C_ne_of_isMaximal N hNmax M' hM'max hEq'
    obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap φ (t1.snoc _ hlt)
    refine ⟨s, ?_, ?_⟩
    · rw [hslen]
      show t.length + 1 = n + 1
      rw [htlen]
    · rw [hslast, RelSeries.last_snoc]
      exact comap_comap_symm φ M
private theorem exists_ltSeries_of_isMaximal_mvPolynomial_uLift (k : Type u) [Field k] (m : ℕ)
    (M : Ideal (MvPolynomial (ULift.{u} (Fin m)) k)) (hM : M.IsMaximal) :
    ∃ s : LTSeries (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k)),
      s.length = m ∧ s.last.asIdeal = M := by
  have := hM
  let φ : MvPolynomial (ULift.{u} (Fin m)) k ≃+* MvPolynomial (Fin m) k :=
    (MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin m) ≃ Fin m)).toRingEquiv
  have hmax :
      (Ideal.comap (φ.symm : MvPolynomial (Fin m) k →+* MvPolynomial (ULift.{u} (Fin m)) k)
        M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (RingEquiv.surjective φ.symm)
  obtain ⟨t, htlen, htlast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial k m _ hmax
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_comap φ t
  refine ⟨s, by rw [hslen, htlen], ?_⟩
  rw [hslast, htlast]
  exact comap_comap_symm φ M
private theorem le_ringKrullDim_stalk_of_chain (X : Scheme.{u}) (x : X) (n : ℕ)
    (z : Fin (n + 1) → X) (hspec : ∀ i, z i ⤳ x)
    (hmono : ∀ i j : Fin (n + 1), i < j → z i ⤳ z j) (hinj : Function.Injective z) :
    ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  choose q hq using fun i => exists_fromSpecStalkPoint_eq_of_specializes X x (hspec i)
  have hstep : ∀ i : Fin n, q i.castSucc < q i.succ := by
    intro i
    have h1 : fromSpecStalkPoint X x (q i.castSucc) ⤳ fromSpecStalkPoint X x (q i.succ) := by
      rw [hq i.castSucc, hq i.succ]
      exact hmono _ _ Fin.castSucc_lt_succ
    have hle : q i.castSucc ≤ q i.succ :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        ((fromSpecStalkPoint_specializes_iff X x _ _).mp h1)
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hz : z i.castSucc = z i.succ := by
      rw [← hq i.castSucc, ← hq i.succ, hEq]
    exact absurd (hinj hz) Fin.castSucc_lt_succ.ne
  have hlen : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk x)) => (t.length : WithBot ℕ∞))
      ⟨n, q, hstep⟩
  have hcast : ((n : ℕ∞) : WithBot ℕ∞) = ((n : ℕ) : WithBot ℕ∞) := by norm_cast
  rw [hcast]
  exact hlen
private theorem le_ringKrullDim_stalk_affineSpace (k : Type u) [Field k] (m : ℕ)
    (x : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))
    (hx : IsClosed ({x} : Set ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))))) :
    ((m : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim
        ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk x) := by
  let e : ↥(AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) ≃ₜ
      PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k) :=
    Scheme.homeoOfIso (AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k))
  have hclosed : IsClosed ({e x} : Set (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin m)) k))) := by
    have h2 := e.isClosedMap _ hx
    rwa [Set.image_singleton] at h2
  have hmax : (e x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (e x)).mp hclosed
  obtain ⟨s, hslen, hslast⟩ := exists_ltSeries_of_isMaximal_mvPolynomial_uLift k m (e x).asIdeal
    hmax
  have hlast : s.last = e x := PrimeSpectrum.ext hslast
  have hspec : ∀ i, (fun j => e.symm (s j)) i ⤳ x := by
    intro i
    have h1 : s i ≤ s.last := s.strictMono.monotone (Fin.le_last i)
    have h2 : (s i) ⤳ s.last := (PrimeSpectrum.le_iff_specializes _ _).mp h1
    have h3 := h2.map e.symm.continuous
    rw [hlast, e.symm_apply_apply] at h3
    exact h3
  have hmono : ∀ i j, i < j → (fun l => e.symm (s l)) i ⤳ (fun l => e.symm (s l)) j := by
    intro i j hij
    have h1 : s i < s j := s.strictMono hij
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp h1.le).map e.symm.continuous
  have hinj : Function.Injective (fun i => e.symm (s i)) := by
    intro i j hij
    exact s.strictMono.injective (e.symm.injective hij)
  have key := le_ringKrullDim_stalk_of_chain
    (AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))) x s.length
    (fun i => e.symm (s i)) hspec hmono hinj
  rw [hslen] at key
  exact key
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [AlgebraicGeometry.Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (hy : IsClosed ({y} : Set Y)) :
    ringKrullDim (Y.presheaf.stalk y) = ((m : ℕ∞) : WithBot ℕ∞) := by
  have hreg : _root_.IsRegularLocalRing
      ((AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k))).presheaf.stalk (c.base y)) :=
    isRegularLocalRing_stalk_affineSpace k (ULift.{u} (Fin m)) (c.base y)
  refine le_antisymm (ringKrullDim_stalk_le_of_etale_affineSpace c y) ?_
  have heq := ringKrullDim_stalk_eq_of_etale c y
  rw [heq]
  exact le_ringKrullDim_stalk_affineSpace k m (c.base y)
    (AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints c hy)
end FunctorialResolution.EmbeddedResolution
