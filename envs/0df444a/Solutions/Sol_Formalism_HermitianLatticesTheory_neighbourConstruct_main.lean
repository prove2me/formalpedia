-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:56.785318+00:00
-- url     : https://prove2.me/submissions/7dc4d13a-fde5-4eaa-990a-de23a60c7171

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_inv
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_span
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_core
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_key
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_avoid
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_hcompl
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_ded
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourBasic_unimod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (P : Ideal R) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) (L : Submodule R V)
    (hLat : Submodule.IsLattice K L) (hL : IsUnimodular h L) (x : V) (hx : x ∈ L)
    (hxP : x ∉ P • L) (hxx : ∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) :
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x := by
  classical
  have hinj := IsFractionRing.injective R K
  set σ := locBasic_sigma hinj hstar with hσdef
  have hσ : ∀ r : R, algebraMap R K (σ r) = star (algebraMap R K r) :=
    fun r => locBasic_sigma_spec hinj hstar r
  have hσσ : ∀ r : R, σ (σ r) = r := fun r =>
    hinj (by rw [hσ, hσ, star_star])
  have hconj : ∀ I : Ideal R, conjIdeal (K := K) (conjIdeal (K := K) I) = I := by
    intro I
    rw [locBasic_conj_eq hinj hstar, locBasic_conj_eq hinj hstar]
    ext r
    rw [Ideal.mem_comap, Ideal.mem_comap, hσσ]
  have hcmax : ∀ I : Ideal R, I.IsMaximal → (conjIdeal (K := K) I).IsMaximal := by
    intro I hI
    rw [locBasic_conj_eq hinj hstar]
    exact Ideal.comap_isMaximal_of_surjective _ (fun r => ⟨_, hσσ r⟩)
  have hPc : (conjIdeal (K := K) P).IsMaximal := hcmax P hP
  have hcmem : ∀ t : R, t ∈ conjIdeal (K := K) P ↔ σ t ∈ P := by
    intro t; rw [locBasic_conj_eq hinj hstar, Ideal.mem_comap]

  have hone : ∀ k : K, k ∈ (1 : Submodule R K) ↔ k ∈ Set.range (algebraMap R K) :=
    fun k => by rw [Submodule.mem_one]; rfl
  have rmul : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a * b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u * v, map_mul _ _ _⟩
  have radd : ∀ a b : K, a ∈ Set.range (algebraMap R K) → b ∈ Set.range (algebraMap R K) →
      a + b ∈ Set.range (algebraMap R K) := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact ⟨u + v, map_add _ _ _⟩
  have rstar : ∀ a : K, a ∈ Set.range (algebraMap R K) → star a ∈ Set.range (algebraMap R K) := by
    rintro _ ⟨u, rfl⟩; exact hstar u

  have hsl : ∀ (a : K) (u v : V), h (a • u) v = star a * h u v := by
    intro a u v; rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
  have hsr : ∀ (a : K) (u v : V), h u (a • v) = a * h u v := by
    intro a u v; rw [map_smul, smul_eq_mul]
  have rs : ∀ (r : R) (u : V), r • u = algebraMap R K r • u := fun r u =>
    (algebraMap_smul K r u).symm
  have hsymm : ∀ u v : V, h v u = star (h u v) := by
    intro u v; rw [← hs.eq u v, starRingEnd_apply]

  have memL : ∀ y : V, y ∈ L ↔ ∀ z ∈ L, h z y ∈ Set.range (algebraMap R K) := by
    intro y
    conv_lhs => rw [← hL]
    rw [dualBasic_mem_dual]
    simp only [hone]
  have hLL : ∀ z ∈ L, ∀ y ∈ L, h z y ∈ Set.range (algebraMap R K) :=
    fun z hz y hy => (memL y).mp hy z hz

  have F2 : ∀ a ∈ invIdeal (K := K) P, ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) :=
    fun a ha => neighbourConstruct_mem_inv.mp ha
  have F3 : ∀ a ∈ invIdeal (K := K) P, ∀ t ∈ conjIdeal (K := K) P,
      star a * algebraMap R K t ∈ Set.range (algebraMap R K) := by
    intro a ha t ht
    have := rstar _ (F2 a ha (σ t) ((hcmem t).mp ht))
    rw [star_mul', hσ, star_star, mul_comm] at this
    exact this
  obtain ⟨r₀, hr₀, hr₀x⟩ := hxx
  have hr₀c : r₀ ∈ conjIdeal (K := K) P := Ideal.mul_le_right hr₀
  have F4 : ∀ a ∈ invIdeal (K := K) P, ∀ b ∈ invIdeal (K := K) P, star a * b * h x x ∈ Set.range (algebraMap R K) := by
    intro a ha b hb
    rw [← hr₀x]
    refine Submodule.mul_induction_on
      (C := fun r => star a * b * algebraMap R K r ∈ Set.range (algebraMap R K)) hr₀ ?_ ?_
    · intro p hp q hq
      have e : star a * b * algebraMap R K (p * q) =
          (algebraMap R K p * b) * (star a * algebraMap R K q) := by rw [map_mul]; ring
      rw [e]
      exact rmul _ _ (F2 b hb p hp) (F3 a ha q hq)
    · intro u v hu hv
      rw [map_add, mul_add]
      exact radd _ _ hu hv

  set Lx := neighbourCore h P L x with hLxdef
  have memLx : ∀ y, y ∈ Lx ↔ y ∈ L ∧ ∃ t ∈ conjIdeal (K := K) P, algebraMap R K t = h x y :=
    fun y => neighbourConstruct_mem_core h P L x y
  have hLxL : Lx ≤ L := fun y hy => ((memLx y).mp hy).1
  have rx : ∀ r : R, r • x ∈ Lx := by
    intro r
    refine (memLx _).mpr ⟨L.smul_mem r hx, r * r₀, Ideal.mul_mem_left _ r hr₀c, ?_⟩
    rw [rs, hsr, map_mul, hr₀x]
  have sLx : ∀ s ∈ conjIdeal (K := K) P, ∀ l ∈ L, s • l ∈ Lx := by
    intro s hs l hl
    obtain ⟨t, ht⟩ := hLL x hx l hl
    refine (memLx _).mpr ⟨L.smul_mem s hl, s * t, Ideal.mul_mem_right _ _ hs, ?_⟩
    rw [rs, hsr, map_mul, ht]

  set M := neighbourOf h P L x with hMdef
  have memM : ∀ z, z ∈ M ↔ ∃ a ∈ invIdeal (K := K) P, ∃ y ∈ Lx, z = a • x + y := by
    intro z
    rw [hMdef, neighbourOf, Submodule.mem_sup]
    constructor
    · rintro ⟨w, hw, y, hy, rfl⟩
      obtain ⟨a, ha, rfl⟩ := neighbourConstruct_mem_span.mp hw
      exact ⟨a, ha, y, hy, rfl⟩
    · rintro ⟨a, ha, y, hy, rfl⟩
      exact ⟨a • x, neighbourConstruct_mem_span.mpr ⟨a, ha, rfl⟩, y, hy, rfl⟩
  have hLxM : Lx ≤ M := fun y hy => (memM y).mpr ⟨0, Submodule.zero_mem _, y, hy, by simp⟩
  have hIxM : ∀ a ∈ invIdeal (K := K) P, a • x ∈ M := fun a ha =>
    (memM _).mpr ⟨a, ha, 0, Submodule.zero_mem _, by simp⟩

  have hD : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L → a ∈ Set.range (algebraMap R K) := by
    intro a ha hax
    by_contra hna
    apply hxP
    refine neighbourConstruct_key (K := K) P hP0 L x ?_
    intro c hc
    obtain ⟨u, b, hub⟩ := neighbourBasic_ded P hP c a (F2 c hc) (F2 a ha) hna
    rw [hub, add_smul, mul_smul, ← rs, ← rs]
    exact L.add_mem (L.smul_mem u hx) (L.smul_mem b hax)
  obtain ⟨c', hc'I, hc'R⟩ : ∃ c' ∈ invIdeal (K := K) P, c' ∉ Set.range (algebraMap R K) := by
    by_contra H
    push Not at H
    apply hxP
    refine neighbourConstruct_key (K := K) P hP0 L x ?_
    intro c hc
    obtain ⟨u, hu⟩ := H c hc
    rw [← hu, ← rs]
    exact L.smul_mem u hx
  have hdec : ∀ c ∈ invIdeal (K := K) P, ∃ u b : R, c = algebraMap R K u + algebraMap R K b * c' :=
    fun c hc => neighbourBasic_ded P hP c c' (F2 c hc) (F2 c' hc'I) hc'R

  have hE : L ⊓ M = Lx := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzL, hzM⟩ := Submodule.mem_inf.mp hz
      obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hzM
      have hax : a • x ∈ L := by
        have := L.sub_mem hzL (hLxL hy)
        simpa using this
      obtain ⟨u, rfl⟩ := hD a ha hax
      rw [← rs]
      exact Lx.add_mem (rx u) hy
    · exact le_inf hLxL hLxM

  have hInt : IsIntegralLat h M := by
    intro z hz w hw
    rw [hone]
    obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hz
    obtain ⟨b, hb, y', hy', rfl⟩ := (memM w).mp hw
    obtain ⟨hyL, t, ht, hty⟩ := (memLx y).mp hy
    obtain ⟨hy'L, t', ht', hty'⟩ := (memLx y').mp hy'
    have e : h (a • x + y) (b • x + y') =
        star a * b * h x x + star a * h x y' + b * h y x + h y y' := by
      simp only [map_add, LinearMap.add_apply, hsl, hsr]; ring
    rw [e, hsymm x y, ← hty, ← hty', ← hσ]
    refine radd _ _ (radd _ _ (radd _ _ (F4 a ha b hb) (F3 a ha t' ht')) ?_) (hLL y hyL y' hy'L)
    rw [mul_comm]; exact F2 b hb (σ t) ((hcmem t).mp ht)

  have eL : (L ⧸ (L ⊓ M).comap L.subtype) ≃ₗ[R] (R ⧸ conjIdeal (K := K) P) := by
    let φ : V → R := fun v => if hv : h x v ∈ Set.range (algebraMap R K) then hv.choose else 0
    have hφ : ∀ v ∈ L, algebraMap R K (φ v) = h x v := by
      intro v hv
      simp only [φ, dif_pos (hLL x hx v hv)]
      exact (hLL x hx v hv).choose_spec
    let g : L →ₗ[R] R :=
      { toFun := fun y => φ y.1
        map_add' := fun y y' => hinj (by
          rw [map_add, hφ _ (y + y').2, hφ _ y.2, hφ _ y'.2, Submodule.coe_add, map_add])
        map_smul' := fun r y => hinj (by
          rw [hφ _ (r • y).2, RingHom.id_apply, smul_eq_mul, map_mul, hφ _ y.2,
            Submodule.coe_smul, rs, hsr]) }
    let f : L →ₗ[R] R ⧸ conjIdeal (K := K) P := (conjIdeal (K := K) P).mkQ ∘ₗ g
    have hker : LinearMap.ker f = (L ⊓ M).comap L.subtype := by
      ext y
      rw [LinearMap.mem_ker, hE, Submodule.mem_comap, Submodule.subtype_apply, memLx]
      show Submodule.Quotient.mk (φ y.1) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hy; exact ⟨y.2, φ y, hy, hφ _ y.2⟩
      · rintro ⟨_, t, ht, hty⟩
        have : t = φ y := hinj (by rw [hty, hφ _ y.2])
        rw [← this]; exact ht
    have hsurj : Function.Surjective f := by
      obtain ⟨y₀, hy₀, hy₀P⟩ : ∃ y₀ ∈ L, φ y₀ ∉ conjIdeal (K := K) P := by
        by_contra H
        push Not at H
        apply hxP
        refine neighbourConstruct_key (K := K) P hP0 L x ?_
        intro a ha
        rw [memL]
        intro z hz
        rw [hsr, hsymm x z, ← hφ z hz, ← hσ, mul_comm]
        exact F2 a ha _ ((hcmem _).mp (H z hz))
      obtain ⟨b, i, hi, hbi⟩ := hPc.exists_inv hy₀P
      intro w
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      refine ⟨(r * b) • ⟨y₀, hy₀⟩, ?_⟩
      show Submodule.Quotient.mk (g ((r * b) • ⟨y₀, hy₀⟩)) = Submodule.Quotient.mk r
      rw [map_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : r * b * g ⟨y₀, hy₀⟩ - r = -(r * i) := by
        show r * b * φ y₀ - r = _
        linear_combination r * hbi
      rw [e]
      exact Submodule.neg_mem _ (Ideal.mul_mem_left _ r hi)
    exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hsurj)

  have hc'M : c' • x ∈ M := hIxM c' hc'I
  have eM : (M ⧸ (L ⊓ M).comap M.subtype) ≃ₗ[R] (R ⧸ P) := by
    let N := (L ⊓ M).comap M.subtype
    let m₀ : M := ⟨c' • x, hc'M⟩
    let g2 : R →ₗ[R] M ⧸ N := LinearMap.toSpanSingleton R (M ⧸ N) (Submodule.Quotient.mk m₀)
    have hmemN : ∀ z : M, z ∈ N ↔ (z : V) ∈ Lx := by
      intro z; simp only [N, Submodule.mem_comap, Submodule.subtype_apply, hE]
    have hsurj2 : Function.Surjective g2 := by
      intro w
      obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
      obtain ⟨a, ha, y, hy, hzy⟩ := (memM z).mp hz
      obtain ⟨u, b, hub⟩ := hdec a ha
      refine ⟨b, ?_⟩
      simp only [g2, LinearMap.toSpanSingleton_apply]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hmemN]
      have e : ((b • m₀ - ⟨z, hz⟩ : M) : V) = -(u • x + y) := by
        rw [Submodule.coe_sub, Submodule.coe_smul]
        show b • (c' • x) - z = _
        rw [hzy, hub, add_smul, mul_smul, ← rs, ← rs]; abel
      rw [e]
      exact Lx.neg_mem (Lx.add_mem (rx u) hy)
    have hker2 : LinearMap.ker g2 = P := by
      ext b
      simp only [g2, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hmemN]
      have e : ((b • m₀ : M) : V) = (algebraMap R K b * c') • x := by
        rw [Submodule.coe_smul]
        show b • (c' • x) = _
        rw [mul_smul, ← rs]
      rw [e]
      constructor
      · intro hb
        by_contra hbP
        have hbI : algebraMap R K b * c' ∈ invIdeal (K := K) P := by
          rw [← Algebra.smul_def]; exact Submodule.smul_mem _ b hc'I
        obtain ⟨v, hv⟩ := hD _ hbI (hLxL hb)
        obtain ⟨e', i, hi, hei⟩ := hP.exists_inv hbP
        apply hc'R
        obtain ⟨w, hw⟩ := F2 c' hc'I i hi
        refine ⟨e' * v + w, ?_⟩
        have : c' = algebraMap R K (e' * b + i) * c' := by rw [hei, map_one, one_mul]
        rw [this]
        simp only [map_add, map_mul]
        rw [hv, hw]; ring
      · intro hb
        obtain ⟨v, hv⟩ := F2 c' hc'I b hb
        rw [← hv, ← rs]
        exact rx v
    exact (g2.quotKerEquivOfSurjective hsurj2).symm.trans (Submodule.quotEquivOfEq _ _ hker2)

  have hloc : ∀ q : Ideal R, q.IsMaximal → q ≠ P → q ≠ conjIdeal (K := K) P →
      loc (K := K) q L = loc (K := K) q M := by
    intro q hq hqP hqPc
    have hqc := hcmax q hq
    obtain ⟨s, hsP, hsq, hsq'⟩ := neighbourConstruct_avoid hP hq hqc (Ne.symm hqP) (by
      intro e; apply hqPc; rw [e, hconj])
    obtain ⟨s', hs'P, hs'q, hs'q'⟩ := neighbourConstruct_avoid hPc hq hqc (Ne.symm hqPc) (by
      intro e; apply hqP; rw [← hconj P, e, hconj])
    have hs := locBasic_mem_hcompl (K := K) q s hsq hsq'
    have hs' := locBasic_mem_hcompl (K := K) q s' hs'q hs'q'
    apply le_antisymm
    · intro z hz
      obtain ⟨s₀, hs₀, hz⟩ := locBasic_mem_locS.mp hz
      refine locBasic_mem_locS.mpr ⟨s' * s₀, Submonoid.mul_mem _ hs' hs₀, ?_⟩
      rw [mul_smul]
      exact hLxM (sLx s' hs'P _ hz)
    · intro z hz
      obtain ⟨s₀, hs₀, hz⟩ := locBasic_mem_locS.mp hz
      refine locBasic_mem_locS.mpr ⟨s * s₀, Submonoid.mul_mem _ hs hs₀, ?_⟩
      obtain ⟨a, ha, y, hy, hzy⟩ := (memM _).mp hz
      rw [mul_smul, hzy, smul_add]
      obtain ⟨u, hu⟩ := F2 a ha s hsP
      rw [rs s (a • x), smul_smul, ← hu, ← rs]
      exact L.add_mem (L.smul_mem u hx) (L.smul_mem s (hLxL hy))

  have hLat' : Submodule.IsLattice K M := by
    have hT : (Submodule.span R {c' • x} ⊔ L).FG := (Submodule.fg_span_singleton _).sup hLat.fg
    have := isNoetherian_of_fg_of_noetherian _ hT
    have hMT : M ≤ Submodule.span R {c' • x} ⊔ L := by
      intro z hz
      obtain ⟨a, ha, y, hy, rfl⟩ := (memM z).mp hz
      obtain ⟨u, b, hub⟩ := hdec a ha
      have e : a • x + y = b • (c' • x) + (u • x + y) := by
        rw [hub, add_smul, mul_smul, ← rs, ← rs]; abel
      rw [e]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _))
        (L.add_mem (L.smul_mem u hx) (hLxL hy))
    refine ⟨Submodule.FG.of_le_of_isNoetherian hMT, ?_⟩
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hsP : σ p ∈ conjIdeal (K := K) P := (hcmem _).mpr (by rw [hσσ]; exact hp)
    have hα : algebraMap R K (σ p) ≠ 0 := by
      rw [hσ, star_ne_zero]; exact (map_ne_zero_iff _ hinj).mpr hp0
    rw [eq_top_iff, ← hLat.span_eq_top, Submodule.span_le]
    intro l hl
    have e : l = (algebraMap R K (σ p))⁻¹ • ((σ p) • l) := by
      rw [rs, smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hLxM (sLx _ hsP l hl)))
  exact ⟨hLat', hInt, neighbourBasic_unimod h hs hstar P hP hPc L M eL eM hL hInt,
    ⟨hloc, ⟨eL⟩, ⟨eM⟩⟩, hE⟩
end Formalism.HermitianLatticesTheory
