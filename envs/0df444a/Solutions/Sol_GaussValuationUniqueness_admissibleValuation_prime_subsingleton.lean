-- Prove2me | solution 1 for GaussValuationUniqueness.admissibleValuation_prime_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:37:03.775285+00:00
-- url     : https://prove2.me/submissions/76545f63-affe-44db-8cdd-371a0c8b3693

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_SHomFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_KerNeBot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_AdmissibleValuationPrimeSubsingleton
import Theorems.Thm_GaussValuationUniqueness_eq_of_le_ht
import Theorems.Thm_GaussValuationUniqueness_exists_smul_of_line
import Theorems.Thm_GaussValuationUniqueness_ker_ne_bot
import Theorems.Thm_GaussValuationUniqueness_mem_vRing_iff
import Theorems.Thm_GaussValuationUniqueness_pos_of_ker
import Theorems.Thm_GaussValuationUniqueness_ratio_eq_of
import Theorems.Thm_GaussValuationUniqueness_sHom_factor
import Theorems.Thm_GaussValuationUniqueness_sImg_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0 NumberField
namespace GaussValuationUniqueness
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
    {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT]
    {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : Data K ι Ω WT A) : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d := by
  intro hd _ c v hAdm hK p1 hp1 p2 hp2
  obtain ⟨hH1, w1, hw1, hv1⟩ := hp1
  obtain ⟨hH2, w2, hw2, hv2⟩ := hp2

  have hRC : d.ResCond c v (d.D - 1) := by
    rcases hAdm.2 with ⟨la, hla, _⟩ | ⟨_, hRC⟩
    · exfalso
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
      have h1 := (hla z).mpr hz
      have hK0 : ((z : 𝓞 K) : K) ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hz0
      rw [hK _ hK0] at h1
      exact lt_irrefl _ h1
    · exact hRC
  obtain ⟨_, j0, hj0, hnn, htr⟩ := hRC
  set a : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c) with ha_def
  have ha : ∀ j, a j ∈ vRing v := fun j => (GaussValuationUniqueness.mem_vRing_iff v _).mpr (hnn j)
  have hQne := GaussValuationUniqueness.ker_ne_bot (D := d.D) v hK j0 a ha (by have := hd.D_ge; omega) htr
  set Q := RingHom.ker (GaussValuationUniqueness.psiR (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩))
    with hQ
  haveI : Q.IsPrime := RingHom.ker_isPrime _

  have hbase := hd.w_base c
  have hline := hd.finrank_one c d.wL
  set b : Fin (d.N + 1) → Ω c := fun j => ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) with hb_def
  have hα : ∀ j, d.w j c = b j • d.w (d.jc c) c := by
    intro j
    obtain ⟨α, hα⟩ := GaussValuationUniqueness.exists_smul_of_line hline (hd.w_mem j c) (hd.w_mem _ c) hbase
    rw [hb_def]
    simp only
    rw [GaussValuationUniqueness.ratio_eq_of hbase hα]
    exact hα
  have hb : b (d.jc c) = 1 := GaussValuationUniqueness.ratio_eq_of hbase (one_smul _ _).symm
  have hb0 : b j0 ≠ 0 := by
    intro h0
    apply hj0
    rw [hα j0, h0, zero_smul]
  have hab : ∀ j, a j = b j * (b j0)⁻¹ := by
    intro j
    apply GaussValuationUniqueness.ratio_eq_of hj0
    rw [hα j, hα j0, smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have ha0 : a j0 = 1 := by rw [hab, mul_inv_cancel₀ hb0]
  have hrel : ∀ i : Fin (d.D + 1), i ≠ 0 →
      ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a j) = 0 := by
    intro i hi
    have rel : ∑ j, sImg (D := d.D) (d.jc c) (d.x c) (i, j) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (b j) = 0 := sImg_rel (d.jc c) b hb i hi
    simp_rw [hab, map_mul, ← mul_assoc]
    rw [← Finset.sum_mul, rel, zero_mul]

  have key : ∀ p, ∀ w ∈ d.GoodP c p, d.Wres c w = v → Q ≤ p := by
    intro p w hw hwv f hf
    have hOv := hw.1
    have hwv' : ∀ t : Ω c, w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) t) = v t := by
      intro t; rw [← hwv]; rfl
    have he : ∀ s, 0 ≤ w (GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) s) := by
      intro s
      rcases s with u | ik
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inl u) =
            d.sH c (MvPolynomial.X ((0, j0) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
      · have e1 : GaussValuationUniqueness.eS (D := d.D) (d.jc c) j0 (d.x c) (Sum.inr ik) =
            d.sH c (MvPolynomial.X ((ik.1, j0.succAbove ik.2) : TVar d.D d.N)) := by
          simp [GaussValuationUniqueness.eS, Data.sH, sHom]
        rw [e1]; exact (hOv.2 _).1
    have hq : MvPolynomial.map (IsLocalRing.residue (vRing v))
        (GaussValuationUniqueness.psiT (D := d.D) v hK j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) = 0 :=
      RingHom.mem_ker.mp hf
    have hpos := GaussValuationUniqueness.pos_of_ker v hwv' _ he _ hq
    have hfac := GaussValuationUniqueness.sHom_factor v hK (d.jc c) j0 (d.x c) a ha ha0 hrel f
    rw [← hfac] at hpos
    exact (hOv.2 f).2.mp hpos
  haveI := hH1.1
  haveI := hH2.1
  have e1 := GaussValuationUniqueness.eq_of_le_ht hH1.2 hQne (key p1 w1 hw1 hv1)
  have e2 := GaussValuationUniqueness.eq_of_le_ht hH2.2 hQne (key p2 w2 hw2 hv2)
  rw [← e1, ← e2]
end GaussValuationUniqueness
