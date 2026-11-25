-- Prove2me | solution 1 for FunctionField.geomH1_rootsOfUnity_equiv_divisibleDivisors_modPow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T08:00:38.682322+00:00
-- url     : https://prove2.me/submissions/609af5fe-9a68-4d49-afb6-98e2f0290dd0

import Mathlib
import Definitions.Def_RPLib_F2_006

set_option autoImplicit false

namespace RamanujanPetersson.SW42Aux

theorem unram_iff (A K : Type) [CommRing A] [Field K] [Algebra A K]
    (L : IntermediateField K (AlgebraicClosure K)) :
    IsUnramifiedSub A K L ↔ ∀ P : Ideal (integralClosure A L), P.IsPrime → ∀ σ : L ≃ₐ[K] L,
      (∀ b : integralClosure A L, ∃ c ∈ P, (c : L) = σ b - b) → σ = 1 := by
  refine forall_congr' fun P => forall_congr' fun _ => ?_
  rw [Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ => imp_congr_left ?_
  rw [AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨c, hc, he⟩ => ?_⟩
  have : c = σ • b - b := Subtype.ext he
  rwa [← this]

end RamanujanPetersson.SW42Aux

open RamanujanPetersson RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh IsDedekindDomain in
set_option maxHeartbeats 4000000 in
theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (F : Type) [Field F] [Algebra Fq F] [Algebra (Polynomial Fq) F] [Algebra (RatFunc Fq) F]
    [IsScalarTower (Polynomial Fq) (RatFunc Fq) F] [IsScalarTower Fq (Polynomial Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F]
    (hk : algebraicClosure Fq F = ⊥)
    (N : ℕ) (hN : (N : F) ≠ 0)
    (CL : ℕ → IntermediateField F (AlgebraicClosure F))
    (hCL : ∀ m, CL m = IntermediateField.adjoin F
      (((Polynomial.X : Polynomial F) ^ (Fintype.card Fq ^ m) - Polynomial.X).rootSet (AlgebraicClosure F)))
    (KU : IntermediateField F (AlgebraicClosure F))
    (hKU : KU = ⨆ L : {L : IntermediateField F (AlgebraicClosure F) //
        FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1}, L.1)
    (Γ : Subgroup (KU ≃ₐ[F] KU))
    (hΓ : ∀ g : KU ≃ₐ[F] KU, g ∈ Γ ↔
      ∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → g x = x)
    (H : Subgroup (Γ →* KUˣ))
    (hH : ∀ χ : Γ →* KUˣ, χ ∈ H ↔ IsLocallyConstant χ ∧ (∀ g : Γ, χ g ^ N = 1) ∧
      ∀ Q : Ideal (integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU),
        Q.IsPrime → Q ≠ ⊥ → ∀ g : Γ,
          (∀ b : integralClosure (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) KU,
            ∃ c ∈ Q, (c : KU) = (g : KU ≃ₐ[F] KU) b - b) → χ g = 1)
    (D : Subgroup KUˣ)
    (hD : ∀ f : KUˣ, f ∈ D ↔ (∀ g ∈ Γ, g (f : KU) = f) ∧
      ∀ m : ℕ, 0 < m → ∀ hm : ((f : KU) : AlgebraicClosure F) ∈ CL m,
        (∀ [IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) (CL m))]
          [IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) (CL m)) (CL m)]
          (v : IsDedekindDomain.HeightOneSpectrum (integralClosure (FunctionField.ringOfIntegers Fq F) (CL m))),
          (N : ℤ) ∣ WithZero.log (v.valuation (CL m) ⟨_, hm⟩)) ∧
        (∀ [IsDedekindDomain (integralClosure
            (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) (CL m))]
          [IsFractionRing (integralClosure
            (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) (CL m)) (CL m)]
          (w : IsDedekindDomain.HeightOneSpectrum (integralClosure
            (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) (CL m))),
          (N : ℤ) ∣ WithZero.log (w.valuation (CL m) ⟨_, hm⟩)))
    (P : Subgroup KUˣ)
    (hP : ∀ f : KUˣ, f ∈ P ↔ ∃ b : KUˣ, (∀ g ∈ Γ, g (b : KU) = b) ∧ f = b ^ N) :
    ∃ Φ : H ≃* D ⧸ P.subgroupOf D,
      (∀ χ ∈ H, ∃ α : KUˣ, ∀ g : Γ, (g : KU ≃ₐ[F] KU) α = (χ g : KU) * α) ∧
      (∀ (χ : H) (α : KUˣ), (∀ g : Γ, (g : KU ≃ₐ[F] KU) α = ((χ : Γ →* KUˣ) g : KU) * α) →
        ∃ hα : α ^ N ∈ D, Φ χ = QuotientGroup.mk (⟨α ^ N, hα⟩ : D)) ∧
      ∀ φ : KU ≃ₐ[F] KU,
        (∀ x : KU, (∃ k : ℕ, 0 < k ∧ x ^ (Fintype.card Fq) ^ k = x) → φ x = x ^ Fintype.card Fq) →
        ∀ (χ χ' : H) (f : D),
          (∀ g g' : Γ, (g' : KU ≃ₐ[F] KU) = φ * g * φ⁻¹ →
            (((χ' : Γ →* KUˣ) g' : KUˣ) : KU) = φ (((χ : Γ →* KUˣ) g : KUˣ) : KU)) →
          Φ χ = QuotientGroup.mk f →
          ∃ hf : Units.map (φ : KU →* KU) (f : KUˣ) ∈ D,
            Φ χ' = QuotientGroup.mk (⟨Units.map (φ : KU →* KU) (f : KUˣ), hf⟩ : D) := by
  classical
  obtain ⟨p, hpc⟩ := CharP.exists Fq
  obtain ⟨e, hp, hq⟩ := FiniteField.card Fq p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := charP_of_injective_algebraMap (algebraMap Fq F).injective p
  have he : 0 < (e : ℕ) := e.pos
  have hset : unramSet (FunctionField.ringOfIntegers Fq F) F =
      {L : IntermediateField F (AlgebraicClosure F) | FiniteDimensional F L ∧ IsGalois F L ∧
        ∀ P : Ideal (integralClosure (FunctionField.ringOfIntegers Fq F) L), P.IsPrime →
          ∀ g : L ≃ₐ[F] L,
            (∀ b : integralClosure (FunctionField.ringOfIntegers Fq F) L, ∃ c ∈ P, (c : L) = g b - b) →
              g = 1} := by
    ext L
    exact and_congr Iff.rfl (and_congr Iff.rfl (SW42Aux.unram_iff _ F L))
  have hKU' : KU = maxUnram (FunctionField.ringOfIntegers Fq F) F := by
    rw [hKU, maxUnram, hset]
    rfl
  subst hKU'
  have : NeZero N := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  have hNA : IsUnit (N : Places.Rfin Fq F) := CP4a.isUnit_cast_Rfin hN
  have hNI : IsUnit (N : Places.Rinf Fq F) := CP4a.isUnit_cast_Rinf hN
  obtain ⟨ζ, hζ, hζg⟩ := CP4a.exists_zeta_geo hq he hN
  have hmemq : ∀ g, g ∈ Γ ↔ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) := fun g =>
    (hΓ g).trans (mem_pi1geo _ _ _ g).symm
  have hmem : ∀ g, g ∈ Γ ↔ g ∈ pi1geo (Places.Rfin Fq F) F (p ^ (e : ℕ)) := fun g => by
    rw [hmemq g, hq]
  have hζΓ : ∀ σ ∈ Γ, σ ζ = ζ := fun σ hσ => hζg σ ((hmemq σ).1 hσ)
  have hCL' : ∀ m, CL m = constLevel F p ((e : ℕ) * m) := by
    intro m
    rw [hCL m, hq, ← pow_mul]
    rfl
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hNq : Nat.Coprime (Fintype.card Fq) N := by rw [hq]; exact coprime_q F p N hN
  -- roots of unity are fixed by `Γ`
  have hfixμ : ∀ x : maxUnram (Places.Rfin Fq F) F, x ^ N = 1 → ∀ g ∈ Γ, g x = x := by
    intro x hx g hg
    have hc : IsConst (Fintype.card Fq) x :=
      isConst_of_pow_eq (m := 1) hq1 one_pos hNq (c := 1) (by simp) one_ne_zero hx
    exact (hΓ g).1 hg x hc
  -- levels
  have hMA : ∀ m, 0 < m → CL m ∈ unramSet (Places.Rfin Fq F) F := fun m hm => by
    rw [hCL' m]; exact constLevel_mem_unramSet _ (Nat.mul_pos he hm)
  have hMI : ∀ m, 0 < m → CL m ∈ unramSet (Places.Rinf Fq F) F := fun m hm => by
    rw [hCL' m]; exact constLevel_mem_unramSet _ (Nat.mul_pos he hm)
  -- `Γ`-fixed elements lie in a level and are unramified at infinity
  have hfixLev : ∀ x : maxUnram (Places.Rfin Fq F) F, (∀ g ∈ Γ, g x = x) →
      ∃ k, 0 < k ∧ (x : AlgebraicClosure F) ∈ CL k := by
    intro x hx
    obtain ⟨k, hk0, hk⟩ := exists_constLevel_of_fixed he (fun σ hσ => hx σ ((hmem σ).2 hσ))
    exact ⟨k, hk0, by rw [hCL' k]; exact hk⟩
  have hfixInf : ∀ x : maxUnram (Places.Rfin Fq F) F, (∀ g ∈ Γ, g x = x) →
      (x : AlgebraicClosure F) ∈ maxUnram (Places.Rinf Fq F) F := by
    intro x hx
    obtain ⟨k, hk0, hk⟩ := hfixLev x hx
    exact (le_iSup (fun L : unramSet (Places.Rinf Fq F) F => (L : IntermediateField F (AlgebraicClosure F)))
      ⟨CL k, hMI k hk0⟩) hk
  -- (M') membership in `D`
  have hMD : ∀ α : (maxUnram (Places.Rfin Fq F) F)ˣ,
      (∀ g ∈ Γ, g ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N) →
      ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) ∈ maxUnram (Places.Rinf Fq F) F →
      α ^ N ∈ D := by
    intro α hfix hinf
    rw [hD]
    refine ⟨fun g hg => by rw [Units.val_pow_eq_pow_val]; exact hfix g hg, fun m hm0 hm => ⟨?_, ?_⟩⟩
    · intro i1 i2 v
      have hpow : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) ^ N =
          (((⟨_, hm⟩ : CL m)) : AlgebraicClosure F) := by
        simp [Units.val_pow_eq_pow_val]
      exact @dvd_log_valuation_of_mem_maxUnram F _ (FunctionField.ringOfIntegers Fq F) _ _ _ _ (CL m)
        (hMA m hm0) (perfect_Rfin Fq F) N _ (α : maxUnram (Places.Rfin Fq F) F).2 _ hpow i1 i2 v
    · intro i1 i2 w
      have hpow : ((α : maxUnram (Places.Rfin Fq F) F) : AlgebraicClosure F) ^ N =
          (((⟨_, hm⟩ : CL m)) : AlgebraicClosure F) := by
        simp [Units.val_pow_eq_pow_val]
      exact dvd_of_mem_maxUnram (Places.Rinf Fq F) (hMI m hm0) (perfect_Rinf Fq F)
        (fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩) hinf hpow w
  have hPD : ∀ b : (maxUnram (Places.Rfin Fq F) F)ˣ,
      (∀ g ∈ Γ, g (b : maxUnram (Places.Rfin Fq F) F) = b) → b ^ N ∈ D := by
    intro b hb
    exact hMD b (fun g hg => by rw [map_pow, hb g hg]) (hfixInf _ hb)
  have hPP : ∀ b : (maxUnram (Places.Rfin Fq F) F)ˣ,
      (∀ g ∈ Γ, g (b : maxUnram (Places.Rfin Fq F) F) = b) → b ^ N ∈ P := fun b hb =>
    (hP _).2 ⟨b, hb, rfl⟩
  -- Kummer characters of elements of `H` and their radicals
  have hMH : ∀ χ ∈ H, ∀ α : (maxUnram (Places.Rfin Fq F) F)ˣ,
      (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χ g : _) * α) →
      α ^ N ∈ D := by
    intro χ hχ α hα
    obtain ⟨-, hχN, hχpar⟩ := (hH χ).1 hχ
    refine hMD α (fun g hg => ?_) ?_
    · rw [map_pow, hα ⟨g, hg⟩, mul_pow, ← Units.val_pow_eq_pow_val, hχN, Units.val_one, one_mul]
    · refine mem_maxUnram_of_fixed CP4a.bdryLift _ fun Q hQ g hg => ?_
      have := hQ.1
      have hgΓ : g ∈ Γ := (hmem g).2 (inertia_le_pi1geo he rfl hg)
      have h1 : χ ⟨g, hgΓ⟩ = 1 := by
        refine hχpar Q hQ.1 hQ.2 ⟨g, hgΓ⟩ fun b => ⟨g • b - b, AddSubgroup.mem_inertia.1 hg b, rfl⟩
      have h2 := hα ⟨g, hgΓ⟩
      rw [h1, Units.val_one, one_mul] at h2
      exact h2
  -- Kummer surjectivity
  have hKS : ∀ χ ∈ H, ∃ α : (maxUnram (Places.Rfin Fq F) F)ˣ,
      ∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χ g : _) * α := by
    intro χ hχ
    obtain ⟨hχlc, hχN, -⟩ := (hH χ).1 hχ
    have hχN' : ∀ g, ((χ g : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) ^ N = 1 :=
      fun g => by rw [← Units.val_pow_eq_pow_val, hχN, Units.val_one]
    let c : Γ → ZMod N := fun g => dlog hζ ((χ g : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F)
    have hc : IsLocallyConstant c :=
      hχlc.comp (fun u : (maxUnram (Places.Rfin Fq F) F)ˣ => dlog hζ (u : maxUnram (Places.Rfin Fq F) F))
    have hhom : ∀ g h : Γ, c (g * h) = c g + c h := by
      intro g h
      apply epow_injective hζ
      rw [epow_add hζ]
      simp only [c]
      rw [epow_dlog hζ (hχN' _), epow_dlog hζ (hχN' _), epow_dlog hζ (hχN' _), map_mul, Units.val_mul]
    obtain ⟨α, hαrad, hαc⟩ := exists_kchar_eq hζ hζΓ c hc hhom
    refine ⟨α, fun g => ?_⟩
    rw [kchar_spec hζ hαrad g, hαc g]
    simp only [c]
    rw [epow_dlog hζ (hχN' _)]
  -- Kummer characters of radicals
  have hWfix : ∀ χ : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ, ∀ α β : (maxUnram (Places.Rfin Fq F) F)ˣ,
      (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χ g : _) * α) →
      (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) β = (χ g : _) * β) →
      ∀ g ∈ Γ, g ((α⁻¹ * β : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) =
        ((α⁻¹ * β : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) := by
    intro χ α β hα hβ g hg
    have h0 : ((χ ⟨g, hg⟩ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) ≠ 0 :=
      Units.ne_zero _
    have hα0 : ((α : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) ≠ 0 := Units.ne_zero _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hα ⟨g, hg⟩, hβ ⟨g, hg⟩]
    field_simp
  -- the quotient class does not depend on the radical
  have hWq : ∀ χ (hχ : χ ∈ H), ∀ α β : (maxUnram (Places.Rfin Fq F) F)ˣ,
      ∀ hα : (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χ g : _) * α),
      ∀ hβ : (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) β = (χ g : _) * β),
      (QuotientGroup.mk (⟨α ^ N, hMH χ hχ α hα⟩ : D) : D ⧸ P.subgroupOf D) =
        QuotientGroup.mk (⟨β ^ N, hMH χ hχ β hβ⟩ : D) := by
    intro χ hχ α β hα hβ
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hPP _ (hWfix χ α β hα hβ)
    convert h using 1
    simp [mul_pow, inv_pow]
  -- the map `H → D / P`
  choose! αK hαK using hKS
  let θf : H → D ⧸ P.subgroupOf D := fun χ =>
    QuotientGroup.mk (⟨αK χ ^ N, hMH χ χ.2 _ (hαK χ χ.2)⟩ : D)
  have θspec : ∀ (χ : H) (α : (maxUnram (Places.Rfin Fq F) F)ˣ)
      (hα : ∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = ((χ : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ) g : maxUnram (Places.Rfin Fq F) F) * α),
      θf χ = QuotientGroup.mk (⟨α ^ N, hMH χ χ.2 α hα⟩ : D) := fun χ α hα =>
    hWq χ χ.2 (αK χ) α (hαK χ χ.2) hα
  have hkmul : ∀ (χ χ' : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ) (α β : (maxUnram (Places.Rfin Fq F) F)ˣ),
      (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χ g : maxUnram (Places.Rfin Fq F) F) * α) →
      (∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) β = (χ' g : maxUnram (Places.Rfin Fq F) F) * β) →
      ∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) ((α * β : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) = ((χ * χ') g : maxUnram (Places.Rfin Fq F) F) * ((α * β : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) := by
    intro χ χ' α β hα hβ g
    rw [Units.val_mul, map_mul, hα g, hβ g, MonoidHom.mul_apply, Units.val_mul]
    ring
  let θ : H →* D ⧸ P.subgroupOf D := MonoidHom.mk' θf (by
    intro χ χ'
    have h1 := θspec (χ * χ') (αK χ * αK χ') (hkmul χ χ' _ _ (hαK χ χ.2) (hαK χ' χ'.2))
    rw [h1, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mul_pow _ _ _))
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro χ hθ
    have hθ' : (QuotientGroup.mk (⟨αK χ ^ N, hMH χ χ.2 _ (hαK χ χ.2)⟩ : D) : D ⧸ P.subgroupOf D) = 1 := hθ
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hθ'
    obtain ⟨b, hb, hbN⟩ := (hP _).1 hθ'
    have hbN' : αK χ ^ N = b ^ N := hbN
    have hr : ((αK χ * b⁻¹ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) ^ N = 1 := by
      rw [← Units.val_pow_eq_pow_val, mul_pow, hbN', inv_pow, mul_inv_cancel, Units.val_one]
    have hfix : ∀ g ∈ Γ, g ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) = αK χ := by
      intro g hg
      have h2 := hfixμ _ hr g hg
      have h3 : ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) = ((αK χ * b⁻¹ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) * b := by
        rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
      rw [h3, map_mul, h2, hb g hg]
    refine Subtype.ext (MonoidHom.ext fun g => Units.ext ?_)
    have h4 := hαK χ χ.2 g
    rw [hfix g g.2] at h4
    have h5 : ((χ : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ) g : maxUnram (Places.Rfin Fq F) F) = 1 :=
      mul_right_cancel₀ (Units.ne_zero (αK χ)) (h4.symm.trans (one_mul _).symm)
    rw [h5]
    rfl
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨hfΓ, hdiv⟩ := (hD f).1 f.2
    obtain ⟨k, hk0, hm⟩ := hfixLev ((f : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) hfΓ
    have hMAk := hMA k hk0
    have hMIk := hMI k hk0
    haveI : FiniteDimensional F (CL k) := hMAk.1
    haveI : IsGalois F (CL k) := hMAk.2.1
    haveI : IsFractionRing (integralClosure (FunctionField.ringOfIntegers Fq F) (CL k)) (CL k) :=
      integralClosure.isFractionRing_of_finite_extension (A := FunctionField.ringOfIntegers Fq F) F (CL k)
    haveI : IsDedekindDomain (integralClosure (FunctionField.ringOfIntegers Fq F) (CL k)) :=
      integralClosure.isDedekindDomain (A := FunctionField.ringOfIntegers Fq F) (K := F) (L := CL k)
    haveI : IsFractionRing (integralClosure
        (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) (CL k)) (CL k) :=
      integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F (CL k)
    haveI : IsDedekindDomain (integralClosure
        (integralClosure (RatFunc.inftyValuation Fq).valuationSubring F) (CL k)) :=
      integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := CL k)
    obtain ⟨hfin, hinf⟩ := hdiv k hk0 hm
    let a : CL k := ⟨_, hm⟩
    have ha : a ≠ 0 := by
      intro h
      apply Units.ne_zero (f : (maxUnram (Places.Rfin Fq F) F)ˣ)
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      exact h'
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure F) (NeZero.pos N)
    have hγU : γ ∈ maxUnram (FunctionField.ringOfIntegers Fq F) F :=
      (forall_dvd_iff_of_range (FunctionField.ringOfIntegers Fq F) hMAk (perfect_Rfin Fq F) hNA ha
        (B := integralClosure (FunctionField.ringOfIntegers Fq F) (CL k))
        (fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩)
        (fun x y hxy => Subtype.ext hxy)).1 (fun v => hfin v) γ hγ
    have hγ0 : (⟨γ, hγU⟩ : maxUnram (Places.Rfin Fq F) F) ≠ 0 := by
      intro h
      have h' : γ = 0 := congrArg Subtype.val h
      apply ha
      apply Subtype.ext
      rw [← hγ, h', zero_pow (NeZero.ne N)]
      rfl
    let α : (maxUnram (Places.Rfin Fq F) F)ˣ := Units.mk0 ⟨γ, hγU⟩ hγ0
    have hαNu : α ^ N = (f : (maxUnram (Places.Rfin Fq F) F)ˣ) := by
      refine Units.ext (Subtype.ext ?_)
      rw [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
      exact hγ
    have hαrad : α ∈ rad Γ N := (mem_rad Γ N α).2 fun σ hσ => by
      rw [← Units.val_pow_eq_pow_val, hαNu]
      exact hfΓ σ hσ
    let χα : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ := MonoidHom.mk' (fun g => Units.mk0 (epow ζ (kchar hζ α g)) (epow_ne_zero hζ _))
      (fun g h => by
        refine Units.ext ?_
        show epow ζ (kchar hζ α (g * h)) = epow ζ (kchar hζ α g) * epow ζ (kchar hζ α h)
        rw [kchar_mul hζ hζΓ hαrad, epow_add hζ])
    have hχαK : ∀ g : Γ, (g : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) α = (χα g : maxUnram (Places.Rfin Fq F) F) * α := fun g => kchar_spec hζ hαrad g
    have hχαH : χα ∈ H := by
      refine (hH χα).2 ⟨(isLocallyConstant_kchar hζ α).comp
        (fun k => Units.mk0 (epow ζ k) (epow_ne_zero hζ k)), fun g => Units.ext (epow_pow_N hζ _), ?_⟩
      intro Q0 hQ hQ0 g hgI
      let Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)) := Q0
      have hgQ : (g : Pi1 (Places.Rfin Fq F) F) ∈ Ideal.inertia (α := proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))
          (Pi1 (Places.Rfin Fq F) F) Q := by
        refine AddSubgroup.mem_inertia.2 fun x => ?_
        obtain ⟨c, hc, hce⟩ := hgI x
        have hc' : c = (g : Pi1 (Places.Rfin Fq F) F) • x - x := Subtype.ext hce
        rw [← hc']
        exact hc
      have hgM : ∀ x : maxUnram (Places.Rfin Fq F) F, (x : AlgebraicClosure F) ∈ CL k → (g : Pi1 (Places.Rfin Fq F) F) x = x :=
        fun x hx => fixed_of_mem_constLevel he (Nat.mul_pos he hk0) (by rw [← hCL' k]; exact hx) g
          ((hmem g).1 g.2)
      have hgα := @fixed_of_dvd _ _ _ _ _ (Places.Rinf Fq F) _ _ _ _ _ hMAk _ _ hNI _ ha _ _ _ _ _
        (fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩) (fun w => hinf w) Q hQ _ hgQ hgM
        (α : maxUnram (Places.Rfin Fq F) F) hγ
      refine Units.ext ?_
      show epow ζ (kchar hζ α g) = 1
      rw [(kchar_eq_iff hζ hαrad g 0).2 (by rw [epow_zero, one_mul]; exact hgα), epow_zero]
    refine ⟨⟨χα, hχαH⟩, ?_⟩
    show θf ⟨χα, hχαH⟩ = _
    rw [θspec ⟨χα, hχαH⟩ α hχαK]
    congr 1
    exact Subtype.ext hαNu
  let Φ : H ≃* D ⧸ P.subgroupOf D := MulEquiv.ofBijective θ ⟨hinj, hsurj⟩
  have hΦ : ∀ χ, Φ χ = θf χ := fun χ => rfl
  refine ⟨Φ, fun χ hχ => ⟨αK χ, hαK χ hχ⟩, fun χ α hα => ⟨hMH χ χ.2 α hα, θspec χ α hα⟩, ?_⟩
  intro φ hφ χ χ' f hrel hf
  have hnorm : ∀ g ∈ Γ, φ⁻¹ * g * φ ∈ Γ := by
    intro g hg
    have h1 := (pi1geo_normal (Places.Rfin Fq F) F (Fintype.card Fq)).conj_mem g ((hmemq g).1 hg) φ⁻¹
    rw [inv_inv] at h1
    exact (hmemq _).2 h1
  have hαk := hαK χ χ.2
  let φα : (maxUnram (Places.Rfin Fq F) F)ˣ := Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) (αK χ)
  have hk' : ∀ g' : Γ, (g' : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) φα = ((χ' : Γ →* (maxUnram (Places.Rfin Fq F) F)ˣ) g' : maxUnram (Places.Rfin Fq F) F) * φα := by
    intro g'
    have hg := hnorm g' g'.2
    have h1 := hrel ⟨φ⁻¹ * g' * φ, hg⟩ g' (by simp [mul_assoc])
    have h2 : (g' : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) (φ ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F)) =
        φ ((φ⁻¹ * (g' : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) * φ) ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F)) := by
      simp [AlgEquiv.mul_apply]
    show (g' : maxUnram (Places.Rfin Fq F) F ≃ₐ[F] maxUnram (Places.Rfin Fq F) F) (φ ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F)) = _ * φ ((αK χ : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F)
    rw [h2, hαk ⟨_, hg⟩, map_mul, ← h1]
  have hf' : (QuotientGroup.mk (⟨αK χ ^ N, hMH χ χ.2 _ hαk⟩ : D) : D ⧸ P.subgroupOf D) =
      QuotientGroup.mk f := hf
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hf'
  obtain ⟨b, hb, hbe⟩ := (hP _).1 hf'
  have hfeq : (f : (maxUnram (Places.Rfin Fq F) F)ˣ) = αK χ ^ N * b ^ N := by
    rw [← hbe]
    simp
  have hφb : ∀ g ∈ Γ, g ((Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) b : (maxUnram (Places.Rfin Fq F) F)ˣ) : maxUnram (Places.Rfin Fq F) F) = Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) b := by
    intro g hg
    have h1 := hb _ (hnorm g hg)
    show g (φ (b : maxUnram (Places.Rfin Fq F) F)) = φ (b : maxUnram (Places.Rfin Fq F) F)
    have h2 : g (φ (b : maxUnram (Places.Rfin Fq F) F)) = φ ((φ⁻¹ * g * φ) (b : maxUnram (Places.Rfin Fq F) F)) := by simp [AlgEquiv.mul_apply]
    rw [h2, h1]
  have hmapf : Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) (f : (maxUnram (Places.Rfin Fq F) F)ˣ) = φα ^ N * Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) b ^ N := by
    rw [hfeq, map_mul, map_pow, map_pow]
  have hfD : Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) (f : (maxUnram (Places.Rfin Fq F) F)ˣ) ∈ D := by
    rw [hmapf]
    exact D.mul_mem (hMH χ' χ'.2 φα hk') (hPD _ hφb)
  refine ⟨hfD, ?_⟩
  rw [hΦ, θspec χ' φα hk', QuotientGroup.eq, Subgroup.mem_subgroupOf]
  show (φα ^ N)⁻¹ * Units.map (φ : maxUnram (Places.Rfin Fq F) F →* maxUnram (Places.Rfin Fq F) F) (f : (maxUnram (Places.Rfin Fq F) F)ˣ) ∈ P
  rw [hmapf, inv_mul_cancel_left]
  exact hPP _ hφb
