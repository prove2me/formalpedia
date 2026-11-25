-- Prove2me | solution 1 for FunctionField.lisseDuality_compactH1_bijective_of_picDivisible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T05:51:42.831842+00:00
-- url     : https://prove2.me/submissions/612b4113-38eb-4dde-bea2-7bc0be46b154

import Mathlib
import Definitions.Def_RPLib_FX_LisseDual_GL
import Definitions.Def_RPLib_FX_LisseDual_BR

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open FunctionField in
theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (p e : ℕ) [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
    (hk : algebraicClosure Fq F = ⊥)
    (l : ℕ) [Fact l.Prime] (hl : (l : F) ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (p ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (hPicU : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) M)]
        [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) M) M]
        (D : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M) → ℤ),
        (Function.support D).Finite →
        ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
          ∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))]
            [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
              ↥(M ⊔ CL m)]
            (w : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
              ↥(M ⊔ CL m)))
            (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) M)),
            (∀ x : integralClosure (FunctionField.ringOfIntegers Fq F) M, x ∈ v.asIdeal ↔
              ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                  AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
            (l : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
    (hPic : ∀ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M → M ≤ KU →
      ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)]
        [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) M]
        (r : ℕ),
        (∀ w : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M),
          Nat.card (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M ⧸
            w.asIdeal) = r) →
        ∀ D : IsDedekindDomain.HeightOneSpectrum
            (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M) → ℤ,
          (Function.support D).Finite → ∑ᶠ w, D w = 0 →
          ∃ m : ℕ, 0 < m ∧ ∃ a : ↥(M ⊔ CL m), a ≠ 0 ∧
            (∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (y : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F)
                ↥(M ⊔ CL m))),
              ((l ^ n : ℕ) : ℤ) ∣ WithZero.log (y.valuation ↥(M ⊔ CL m) a)) ∧
            ∀ [IsDedekindDomain (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))]
              [IsFractionRing (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m))
                ↥(M ⊔ CL m)]
              (w : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F)
                ↥(M ⊔ CL m)))
              (v : IsDedekindDomain.HeightOneSpectrum
                (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M)),
              (∀ x : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) M,
                x ∈ v.asIdeal ↔ ∃ y ∈ w.asIdeal, ((y : ↥(M ⊔ CL m)) :
                    AlgebraicClosure F) = ((x : M) : AlgebraicClosure F)) →
              ((l ^ n : ℕ) : ℤ) ∣ D v + WithZero.log (w.valuation ↥(M ⊔ CL m) a))
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (P : S → Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU))
    (hP : ∀ s, (P s).IsPrime ∧ P s ≠ ⊥)
    (hcover : ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
      Q.IsPrime → Q ≠ ⊥ → ∃ s, ∃ g ∈ Γ,
        ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ Q ↔ ∃ c ∈ P s, (b : KU) = g (c : KU))
    (hdisj : ∀ s s', ∀ g ∈ Γ,
      (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, b ∈ P s' ↔ ∃ c ∈ P s, (b : KU) = g (c : KU)) → s = s')
    (I : S → Subgroup (KU ≃ₐ[F] KU))
    (hI : ∀ s (g : KU ≃ₐ[F] KU), g ∈ I s ↔
      ∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU, ∃ c ∈ P s, (c : KU) = g (b : KU) - b)
    (E : IntermediateField F (AlgebraicClosure F))
    (hE : FiniteDimensional F E ∧ IsGalois F E ∧
      ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) E), P.IsPrime →
        ∀ g : E ≃ₐ[F] E,
          (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) E, ∃ c ∈ P, (c : E) = g b - b) →
            g = 1)
    (hEU : E ≤ KU)
    (Gf : Type) [Group Gf] [Finite Gf] (π : (KU ≃ₐ[F] KU) →* Gf)
    (hπ : ∀ g : KU ≃ₐ[F] KU, π g = 1 ↔ ∀ x : KU, (x : AlgebraicClosure F) ∈ E → g x = x)
    (hfin : {y : ↥(Γ.subgroupOf π.ker) → ZMod l |
      IsLocallyConstant y ∧ ∀ a b, y (a * b) = y a + y b}.Finite)
    (Λ : Type) [CommRing Λ] [Finite Λ] [Module.Injective Λ Λ] (hΛ : ((l ^ n : ℕ) : Λ) = 0)
    (hsep : ∀ (N : Type) [AddCommGroup N] [Module Λ N] [Finite N] (m : N), m ≠ 0 →
      ∃ φ : N →ₗ[Λ] Λ, φ m ≠ 0)
    (σ : Representation Λ (KU ≃ₐ[F] KU) Λ) (hσ : IsOpen (σ.ker : Set (KU ≃ₐ[F] KU)))
    (htriv : ∀ g ∈ Γ, ∀ x : Λ, σ g x = x)
    (M : Type) [AddCommGroup M] [Module Λ M] [Finite M] (τ : Representation Λ Gf M) :
    ∃ t : S → Γ, (∀ s, (t s : KU ≃ₐ[F] KU) ∈ I s) ∧
      (∀ (c : Γ → M) (d : Γ → (M →ₗ[Λ] Λ)),
        (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + τ (π g) (c h)) →
        (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
        ∃ u : Γ → Λ, IsLocallyConstant u ∧
          ∀ g h : Γ, (Representation.linHom (τ.comp π) σ) g (d h) (c g) = σ g (u h) - u (g * h) + u g) ∧
      ∃ pair : (Γ → M) × (S → M) → (Γ → (M →ₗ[Λ] Λ)) → Λ,
        (∀ (x : (Γ → M) × (S → M)) (d : Γ → (M →ₗ[Λ] Λ)) (u : Γ → Λ),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) →
          (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
          (IsLocallyConstant u ∧
            ∀ g h : Γ, (Representation.linHom (τ.comp π) σ) g (d h) (x.1 g) = σ g (u h) - u (g * h) + u g) →
          pair x d = ∑ s, (d (t s) (x.2 s) - u (t s))) ∧
        (∀ x : (Γ → M) × (S → M),
          (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
            ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) →
          (∀ d : Γ → (M →ₗ[Λ] Λ),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
              pair x d = 0) →
          ∃ m : M, (∀ g : Γ, x.1 g = τ (π g) m - m) ∧ ∀ s, x.2 s = m) ∧
        ∀ f : (Γ → (M →ₗ[Λ] Λ)) → Λ,
          (∀ d d' : Γ → (M →ₗ[Λ] Λ),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
            (IsLocallyConstant d' ∧ ∀ g h, d' (g * h) = d' g + (Representation.linHom (τ.comp π) σ) g (d' h)) →
              f (d + d') = f d + f d') →
          (∀ (a : Λ) (d : Γ → (M →ₗ[Λ] Λ)),
            (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
              f (a • d) = a * f d) →
          (∀ φ : M →ₗ[Λ] Λ, f (fun g => (Representation.linHom (τ.comp π) σ) g φ - φ) = 0) →
          ∃ x : (Γ → M) × (S → M),
            (IsLocallyConstant x.1 ∧ (∀ g h, x.1 (g * h) = x.1 g + τ (π g) (x.1 h)) ∧
              ∀ s (g : Γ), (g : KU ≃ₐ[F] KU) ∈ I s → x.1 g = τ (π g) (x.2 s) - x.2 s) ∧
            ∀ d : Γ → (M →ₗ[Λ] Λ),
              (IsLocallyConstant d ∧ ∀ g h, d (g * h) = d g + (Representation.linHom (τ.comp π) σ) g (d h)) →
                pair x d = f d := by
  open RamanujanPetersson in
  classical
  -- `K_U = maxUnram`
  have hset : unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (SW38B.unram_iff _ F L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have hCL' : CL = Kummer.constLevel F p := funext hCL
  subst hCL'
  have hΓ' : Γ = CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq) := by
    ext g
    rw [hΓ, CurveCoh.mem_pi1geo]
    rfl
  subst hΓ'
  -- the divisibility hypotheses in library form
  have hPicU' : CdOne.PicDivU (Places.Rfin Fq F) F p l := by
    intro M hM hMU i1 i2 D hD
    obtain ⟨m, hm, a, ha, H⟩ := @hPicU M hM hMU i1 i2 D hD
    refine ⟨m, hm, a, ha, ?_⟩
    intro i3 i4 w
    exact @H i3 i4 w _ (@SW38B.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w)
  have hPic' : Residue.PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p (l ^ n) := by
    intro M hM hMU i1 i2 r hr D hD hsum
    obtain ⟨m, hm, a, ha, H1, H2⟩ := @hPic M hM hMU i1 i2 r hr D hD hsum
    refine ⟨m, hm, a, ha, by intro i5 i6 y; exact @H1 i5 i6 y, ?_⟩
    intro i3 i4 w
    exact @H2 i3 i4 w _ (@SW38B.under_iff _ _ _ _ _ _ _ _ _ le_sup_left i1 i3 w)
  -- boundary data
  let D : CurveCoh.BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S :=
    { B := CurveCoh.IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F)
      B_smul := fun g Q hQ => CurveCoh.isBdryPrime_smul _ _ _ g hQ
      P := P
      mem := hP
      cover := fun Q hQ => by
        obtain ⟨s, g, hg, hb⟩ := hcover Q hQ.1 hQ.2
        exact ⟨s, g, hg, Ideal.ext fun b => (hb b).trans (SW38B.mem_smul_iff _ g (P s) b).symm⟩
      disj := fun s s' g hg he => hdisj s s' g hg fun b => by
        rw [he]
        exact SW38B.mem_smul_iff _ g (P s) b }
  have hI' : I = D.inertia := by
    funext s
    ext g
    rw [hI]
    show _ ↔ g ∈ CurveCoh.BdryData.inertia D s
    rw [CurveCoh.BdryData.inertia, AddSubgroup.mem_inertia]
    refine forall_congr' fun b => ⟨fun ⟨c, hc, he⟩ => ?_, fun h => ⟨_, h, rfl⟩⟩
    have : c = g • b - b := Subtype.ext he
    rwa [← this]
  subst hI'
  have htr : ∀ (g : CurveCoh.pi1geo (FunctionField.ringOfIntegers Fq F) F (Fintype.card Fq)) (x : Λ),
      σ g x = x := fun g x => htriv g g.2 x
  have hM : E ∈ unramSet (Places.Rfin Fq F) F := by
    show E ∈ unramSet (FunctionField.ringOfIntegers Fq F) F
    rw [hset]
    exact hE
  have hπM : ∀ g, π g = 1 ↔ g ∈ (IntermediateField.restrict hEU).fixingSubgroup := fun g => by
    rw [hπ g, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h x ((IntermediateField.mem_restrict hEU x).1 hx),
      fun h x hx => h x ((IntermediateField.mem_restrict hEU x).2 hx)⟩
  obtain ⟨hπo, t, DD, hv, hbij⟩ := SW38Sol.core Fq F p e hq he hk l hl n hn hPicU' hPic' S D
    (fun Q => Iff.rfl) E hM hE.1 hEU Gf π hπM hfin Λ hΛ hsep σ hσ htr M τ
  refine ⟨CupDuality.tG t, fun s => (Subgroup.mem_inf.1 (t s).2).2,
    fun c d hc hd => SW38B.lpair_prim hv hσ (CupDuality.isOpen_comp π hπo τ) c d hc hd,
    SW38B.lpair hv DD hσ (CupDuality.isOpen_comp π hπo τ),
    fun x d u hx hd hu => SW38B.lpair_formula hv DD hσ _ x d u ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩ hd hu,
    fun x hx h0 => SW38B.lpair_inj hv DD hσ _ hbij x ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩ h0,
    fun f hadd hsmul hcob => ?_⟩
  obtain ⟨x, hx, hxf⟩ := SW38B.lpair_surj hv DD hσ (CupDuality.isOpen_comp π hπo τ) hbij f hadd hsmul hcob
  exact ⟨x, ⟨hx.1.1, hx.1.2, hx.2⟩, hxf⟩
