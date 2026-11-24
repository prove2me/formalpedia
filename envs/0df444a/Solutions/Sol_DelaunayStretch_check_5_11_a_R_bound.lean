-- Prove2me | solution 1 for DelaunayStretch.check_5_11_a_R_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:35:49.616298+00:00
-- url     : https://prove2.me/submissions/9b1e0ac9-f5bd-44d4-9b2b-ce4800bdade3

import Mathlib
import Definitions.Def_DelaunayStretch_HstarCoefficients
open DelaunayStretch

namespace CheckA

/-! ## Part 1. Cubic B-splines: local polynomial pieces, nonnegativity, partition of unity -/

/-- Polynomials in one variable as coefficient lists (lowest degree first). -/
def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

/-- `(a + b s) * p`. -/
def pmulLin (a b : ℚ) (p : List ℚ) : List ℚ := padd (p.map (a * ·)) (0 :: p.map (b * ·))

/-- Evaluation of a coefficient list at a real point (Horner). -/
noncomputable def peval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: p, s => (c : ℝ) + s * peval p s

lemma peval_padd : ∀ (p q : List ℚ) (s : ℝ), peval (padd p q) s = peval p s + peval q s
  | [], q, s => by simp [padd, peval]
  | a :: p, [], s => by simp [padd, peval]
  | a :: p, b :: q, s => by
      simp only [padd, peval, peval_padd p q s]; push_cast; ring

lemma peval_map (a : ℚ) : ∀ (p : List ℚ) (s : ℝ), peval (p.map (a * ·)) s = a * peval p s
  | [], s => by simp [peval]
  | c :: p, s => by
      simp only [List.map_cons, peval, peval_map a p s]; push_cast; ring

lemma peval_pmulLin (a b : ℚ) (p : List ℚ) (s : ℝ) :
    peval (pmulLin a b p) s = ((a : ℝ) + b * s) * peval p s := by
  simp only [pmulLin, peval_padd, peval, peval_map]; push_cast; ring

/-- Rational copy of `splineKnot`. -/
def knotQ (j : ℕ) : ℚ := max 0 (min 1 (((j : ℚ) - 3) / 32))

lemma knotQ_cast (j : ℕ) : ((knotQ j : ℚ) : ℝ) = splineKnot j := by
  simp [knotQ, splineKnot]

/-- The polynomial (in the local variable `s = 32 τ - k`) representing the B-spline
`N_{j,p}` on the knot interval `[k/32, (k+1)/32]`. -/
def bpoly (k : ℕ) : ℕ → ℕ → List ℚ
  | 0, j => [if j = k + 3 then 1 else 0]
  | p + 1, j =>
      padd (pmulLin (((k : ℚ) / 32 - knotQ j) / (knotQ (j + p + 1) - knotQ j))
                    ((1 / 32) / (knotQ (j + p + 1) - knotQ j)) (bpoly k p j))
           (pmulLin ((knotQ (j + p + 2) - (k : ℚ) / 32) / (knotQ (j + p + 2) - knotQ (j + 1)))
                    ((-1 / 32) / (knotQ (j + p + 2) - knotQ (j + 1))) (bpoly k p (j + 1)))

lemma splineKnot_mono {i j : ℕ} (h : i ≤ j) : splineKnot i ≤ splineKnot j := by
  unfold splineKnot
  have : ((i : ℝ) - 3) / 32 ≤ ((j : ℝ) - 3) / 32 := by
    have : (i : ℝ) ≤ j := by exact_mod_cast h
    linarith
  exact max_le_max le_rfl (min_le_min le_rfl this)

lemma splineKnot_le_one (j : ℕ) : splineKnot j ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma splineKnot_k3 (k : ℕ) (hk : k ≤ 32) : splineKnot (k + 3) = (k : ℝ) / 32 := by
  unfold splineKnot
  have h1 : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  rw [show ((k : ℝ) + 3 - 3) / 32 = (k : ℝ) / 32 by ring]
  rw [min_eq_right (by linarith), max_eq_right (by positivity)]

lemma splineKnot_k4 (k : ℕ) (hk : k ≤ 31) : splineKnot (k + 3 + 1) = ((k : ℝ) + 1) / 32 := by
  have := splineKnot_k3 (k + 1) (by omega)
  rw [show k + 3 + 1 = k + 1 + 3 by ring, this]; push_cast; ring

lemma deg0_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) (j : ℕ) :
    bsplineDeg0 j τ = if j = k + 3 then 1 else 0 := by
  have hk' : (k : ℝ) ≤ 31 := by exact_mod_cast hk
  unfold bsplineDeg0
  by_cases hj : j = k + 3
  · subst hj
    rw [if_pos rfl, if_pos]
    rcases h1 with h1 | ⟨h31, hτ⟩
    · left
      rw [splineKnot_k3 k (by omega), splineKnot_k4 k hk]
      exact ⟨h0, h1⟩
    · right; exact ⟨by omega, hτ⟩
  · rw [if_neg hj, if_neg]
    rintro (⟨ha, hb⟩ | ⟨hj34, hτ⟩)
    · rcases h1 with h1 | ⟨h31, hτ⟩
      · rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
        · have := splineKnot_mono (show j + 1 ≤ k + 3 by omega)
          rw [splineKnot_k3 k (by omega)] at this
          linarith
        · have := splineKnot_mono (show k + 3 + 1 ≤ j by omega)
          rw [splineKnot_k4 k hk] at this
          linarith
      · have := splineKnot_le_one (j + 1)
        linarith
    · rcases h1 with h1 | ⟨h31, hτ'⟩
      · linarith
      · omega

lemma basis_local (k : ℕ) (hk : k ≤ 31) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    ∀ p j, bsplineBasis p j τ = peval (bpoly k p j) (32 * τ - k)
  | 0, j => by
      rw [bsplineBasis, deg0_local k hk τ h0 h1 j]
      simp only [bpoly, peval]
      split_ifs <;> simp
  | p + 1, j => by
      rw [bsplineBasis, bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        ← basis_local k hk τ h0 h1 p j, ← basis_local k hk τ h0 h1 p (j + 1)]
      push_cast [knotQ_cast]
      ring

lemma peval_bpoly_zero (k : ℕ) (s : ℝ) : ∀ p j, k + 3 < j → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin, peval_bpoly_zero k s p j hj,
        peval_bpoly_zero k s p (j + 1) (by omega)]
      ring

/-- Nonnegativity of the four Bernstein coefficients of a cubic on `[0, 1]`. -/
def cubicOK : List ℚ → Bool
  | [c0, c1, c2, c3] =>
      decide (0 ≤ c0) && decide (0 ≤ c0 + c1 / 3) && decide (0 ≤ c0 + 2 * c1 / 3 + c2 / 3) &&
        decide (0 ≤ c0 + c1 + c2 + c3)
  | _ => false

lemma cubic_nonneg (p : List ℚ) (h : cubicOK p = true) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ peval p s := by
  rcases p with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, p⟩⟩⟩⟩⟩ <;>
    simp only [cubicOK, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  have e : peval [c0, c1, c2, c3] s =
      (c0 : ℝ) * (1 - s) ^ 3 + 3 * ((c0 + c1 / 3 : ℚ) : ℝ) * s * (1 - s) ^ 2 +
        3 * ((c0 + 2 * c1 / 3 + c2 / 3 : ℚ) : ℝ) * s ^ 2 * (1 - s) +
        ((c0 + c1 + c2 + c3 : ℚ) : ℝ) * s ^ 3 := by
    simp only [peval]; push_cast; ring
  have a0 : (0 : ℝ) ≤ (c0 : ℝ) := by exact_mod_cast h0
  have a1 : (0 : ℝ) ≤ ((c0 + c1 / 3 : ℚ) : ℝ) := by exact_mod_cast h1
  have a2 : (0 : ℝ) ≤ ((c0 + 2 * c1 / 3 + c2 / 3 : ℚ) : ℝ) := by exact_mod_cast h2
  have a3 : (0 : ℝ) ≤ ((c0 + c1 + c2 + c3 : ℚ) : ℝ) := by exact_mod_cast h3
  have hs' : 0 ≤ 1 - s := by linarith
  rw [e]
  have t0 := mul_nonneg a0 (pow_nonneg hs' 3)
  have t1 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) a1) hs0)
    (pow_nonneg hs' 2)
  have t2 := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) a2)
    (pow_nonneg hs0 2)) hs'
  have t3 := mul_nonneg a3 (pow_nonneg hs0 3)
  linarith

lemma peval_bpoly_zero_low (k : ℕ) (s : ℝ) : ∀ p j, j + p < k + 3 → peval (bpoly k p j) s = 0
  | 0, j, hj => by
      simp only [bpoly, peval]
      rw [if_neg (by omega)]; simp
  | p + 1, j, hj => by
      rw [bpoly, peval_padd, peval_pmulLin, peval_pmulLin,
        peval_bpoly_zero_low k s p j (by omega), peval_bpoly_zero_low k s p (j + 1) (by omega)]
      ring

theorem check_nonneg : ∀ k < 32, ∀ d < 4, cubicOK (bpoly k 3 (k + d)) = true := by
  decide +kernel

theorem check_pou : ∀ k < 32,
    padd (padd (padd (bpoly k 3 k) (bpoly k 3 (k + 1))) (bpoly k 3 (k + 2))) (bpoly k 3 (k + 3))
      = [1, 0, 0, 0] := by
  decide +kernel

lemma exists_interval (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∃ k : ℕ, k ≤ 31 ∧ (k : ℝ) / 32 ≤ τ ∧ (τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) := by
  by_cases hτ : τ = 1
  · refine ⟨31, le_rfl, ?_, Or.inr ⟨rfl, hτ⟩⟩
    rw [hτ]; norm_num
  · have hlt : τ < 1 := lt_of_le_of_ne h1 hτ
    have hf1 := Nat.floor_le (show (0 : ℝ) ≤ 32 * τ by linarith)
    have hf2 := Nat.lt_floor_add_one (32 * τ)
    refine ⟨⌊32 * τ⌋₊, ?_, ?_, Or.inl ?_⟩
    · have : (⌊32 * τ⌋₊ : ℝ) < 32 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · linarith
    · linarith

lemma local_s_bounds (k : ℕ) (τ : ℝ) (h0 : (k : ℝ) / 32 ≤ τ)
    (h1 : τ < ((k : ℝ) + 1) / 32 ∨ (k = 31 ∧ τ = 1)) :
    0 ≤ 32 * τ - k ∧ 32 * τ - k ≤ 1 := by
  constructor
  · linarith
  · rcases h1 with h1 | ⟨h31, hτ⟩
    · linarith
    · subst h31; rw [hτ]; norm_num

/-- **Nonnegativity of the cubic B-splines** on `[0, 1]`. -/
theorem bspline_nonneg (l : ℕ) (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) : 0 ≤ bspline l τ := by
  obtain ⟨k, hk, hk0, hk1⟩ := exists_interval τ h0 h1
  rw [bspline, basis_local k hk τ hk0 hk1]
  obtain ⟨hs0, hs1⟩ := local_s_bounds k τ hk0 hk1
  by_cases hl1 : l < k
  · rw [peval_bpoly_zero_low k _ 3 l (by omega)]
  by_cases hl2 : k + 3 < l
  · rw [peval_bpoly_zero k _ 3 l hl2]
  obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
  exact cubic_nonneg _ (check_nonneg k (by omega) d (by omega)) _ hs0 hs1

/-- **Partition of unity of the cubic B-splines** on `[0, 1]`. -/
theorem bspline_sum_one (τ : ℝ) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    ∑ l : Fin 35, bspline l τ = 1 := by
  obtain ⟨k, hk, hk0, hk1⟩ := exists_interval τ h0 h1
  rw [Fin.sum_univ_eq_sum_range (fun l => bspline l τ) 35]
  simp only [bspline, basis_local k hk τ hk0 hk1]
  rw [← Finset.sum_subset (s₁ := Finset.Ico k (k + 4))]
  · rw [Finset.sum_Ico_eq_sum_range, show k + 4 - k = 4 by omega]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
    rw [← peval_padd, ← peval_padd, ← peval_padd, check_pou k (by omega)]
    simp [peval]
  · intro x hx
    simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hx
    rcases hx with hx | hx
    · exact peval_bpoly_zero_low k _ 3 x (by omega)
    · exact peval_bpoly_zero k _ 3 x (by omega)

end CheckA

namespace CheckA

/-! ## Part 2. Bernstein polynomials of degree 5 and subdivision at `1/2` -/

lemma bernstein_nonneg' (d i : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ DelaunayStretch.bernstein d i x :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg (sub_nonneg.2 h1) _)

lemma bernstein5_sum (x : ℝ) : ∑ m : Fin 6, DelaunayStretch.bernstein 5 m x = 1 := by
  simp only [Fin.sum_univ_six, DelaunayStretch.bernstein]
  norm_num [Nat.choose]
  ring

/-- `32 ×` the subdivision matrix: `𝓑⁵ᵢ((h + s)/2) = Σ_m (LN h i m / 32) 𝓑⁵_m(s)`. -/
def LN (h i m : ℕ) : ℤ :=
  if h = 0 then (m.choose i : ℤ) * 2 ^ (5 - m)
  else ((5 - m).choose (5 - i) : ℤ) * 2 ^ m

lemma bernstein_subdiv (h : ℕ) (hh : h < 2) (i : Fin 6) (s : ℝ) :
    DelaunayStretch.bernstein 5 i (((h : ℝ) + s) / 2) =
      ∑ m : Fin 6, ((LN h i m : ℤ) : ℝ) / 32 * DelaunayStretch.bernstein 5 m s := by
  interval_cases h <;> fin_cases i <;>
    simp [Fin.sum_univ_six, DelaunayStretch.bernstein, LN, Nat.choose] <;> ring

/-! ## Part 3. The coefficients `R_{ijl}` as integers over `5·10²⁵` and the subdivided bound -/

def hstarZStored : List (List ℤ) := [
  [-38688633885920787902060, -36538505256730548410442, -30184821522607809604336, -17211955469600006364506, -3514687955168807710046, 8189042032785022606020, 15181295516358864282736, 17665693480321248233908, 15845856889444418469206, 9925406748493192806572, 107964017240743529642, -12536465902831940105772, -26937877650236442652130, -42026265823491774853620, -56731625056110449536668, -68711738127691986212688, -75624387832833119571196, -75127356956132440849640, -64878428282188541285468, -48870374730923415218158, -31095969197263698357018, -15547984601131385041526, -6219193837453110980990, -1554798460613045676756, 0, 0, 0, -35149723073676562500000, -140598892294706250000000, -351497230736765625000000, -702994461473531250000000, -949042522989267187500000, -843593353768237500000000, -374930379452550000000000, 0],
  [76673465250416104966292, 78193357845173805882085, 73272562241603978227556, 49021779381704745438960, 14913559986973146769070, -22039943019129388562080, -54826576718140503060490, -74039128653448624073090, -70270386373441250672844, -34113137416507738480648, 43839830678962556882602, 137724432825978888776070, 221676583947548654010988, 269832198951682034220486, 256327192756387354489762, 203201466793516314504050, 132494922479923398770482, 66247461242461235248258, 26498984497984308444510, 6624746125745845042636, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [-84181106714473474131049, -91455608415082697065032, -87644929777206889590600, -50983180065648857194246, -7509012876900723113096, 18644257511483293152940, 3343316801952685199816, -58706770412816346843084, -172800939560143889750512, -344234126052352815119118, -578301265321762281449688, -815409591170464108723064, -995966337425545475550258, -1060378737889098201912112, -949054026388209466419638, -729359629629774009536418, -468662974315687500000000, -234331487157843750000000, -93732594863137500000000, -23433148715784375000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [52715663442080073884790, 61874045343855056623892, 64923107310772459749278, 42128387945509761954998, 10400149218911703404822, -11826815877225236229532, -6117714386098079358584, 40863192113796746947796, 142451642028965600441636, 311983373750917623696862, 562794125706155461369638, 826273204044149335883948, 1033809914954362043472048, 1116793564601261021736024, 1006613459154312780003996, 776555896024647730864016, 499907172603400000000000, 249953586301700000000000, 99981434520680000000000, 24995358630170000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [38688633885920787902060, 40838762515111027393678, 41728504229623970996802, 36073548524205538353566, 26671002901013087480856, 16762845729458591649188, 9591055353958665498908, 4612018302700585713994, 1282121093873485526356, -942249739336286653994, -2604707693736812773248, -3678699879914672774230, -4137673403457374873730, -3955075379950570740606, -3104352914981768591648, -4021934459936995540772, -9144248431208776619656, -20907723280183138942216, -41748787428251679266164, -67600912686054344905060, -94397570864231083172464, -118072233763423697929868, -134558373184273993038764, -128397958242210864240482, -84132958047664135550318, 13694658283937297290398, 180542921647162681992404, 341572441938525702434270, 421943829074536329398702, 346817692946709175038236, 41354643466555138409544, -289804195116347648712786, -442017698552421054554166, -287769061238866220776682, -112606811973591351128580],
  [0, -21936781085193314662668, -52240266353217182586308, -67849935085267493099812, -64478716179436033348458, -52991281167826524439344, -44252301602538974383704, -37152397278570810029344, -30582188025912960306308, -23432293649560995514470, -14593333974506772857840, -8531166233992773878584, -9711647636266121488698, -22600635429566512408450, -51663986827140141275870, -95259064599090671383658, -151743231510522694298480, -219473850321541729860968, -296808283797252369637788, -366823928938406395466594, -412598182745755589185040, -417208442210053589178712, -363732104327053105559230, -275478708060542792858200, -175757792364313162155160, -87878896177157509351546, -35151558472862632431032, -46280927563470658107758, -149972151781020000000000, -374930379452550000000000, -749860758905100000000000, -1152910916816591250000000, -1462228479864945000000000, -1524716876440370000000000, -1499721517810200000000000],
  [-22201687984825218632080, 11412259775843957508588, 60112327510948642800130, 94050156115421239761496, 105346922002240828123806, 110473835439441150948866, 125902106715052238202618, 144482957755436691937492, 159067610501954329384020, 162507286890965896046700, 147653208858832137430030, 121111877584189759245968, 89489794230678252028370, 59393459976934321489194, 37429375991596529888330, 22174836500857602564084, 12207135715913049676660, 6103567857956524838330, 2441427143182609935332, 610356788295188346850, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [27877367487057005277302, -4530089793445440489681, -50647258012768727264122, -77721959986196847290416, -76687800173574726803870, -61536967130661488180418, -46261649423214397248062, -8426197305596177373328, 74405038992825806707428, 224667709222687903353714, 464797463139625532651072, 725461232395300133162768, 937325948631375000000000, 1031058543494512500000000, 937325948631375000000000, 726427610189315625000000, 468662974315687500000000, 234331487157843750000000, 93732594863137500000000, 23433148715784375000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 14271242768386841852938, 35309959949408512989084, 49230394174176782838964, 50386850382670760141424, 43652992082884566436230, 33902482812806753619352, 32083003510585255230664, 49142235124366148262108, 96027858607294581431660, 183687554902517560005228, 283417507050775034643552, 366513898077809740829270, 404272911034359772675190, 367990728936169722211882, 285386648977253492185062, 184179968326629626710276, 92089984163314813355138, 36835993666325739687262, 9208998412832131127290, 0, 0, 0, 0, 0, 0, 0, -37278637812058642794374, -149114551253233642903530, -372786378135583643121842, -745572756266168214517650, -1006523220960576857530336, -894687307519401857421180, -397638803341956381076080, 0],
  [-52715663442080073884790, -43557281540305091145688, -32763309225115582376536, -32238216224250178755102, -40476479802122558591780, -50575591090547004442558, -55633041201341511959288, -54482492000979522677942, -45957605365932621586560, -28892043157675178495080, -2119467237681563213440, 4164201577460181418810, -40236957503842628807710, -165518865298178036732550, -401877442602137798291124, -677568045776032247895652, -920846031185170791684388, -1059966755184864692343518, -1023185574130425212559228, -877710582565019833035200, -690749875016818819297014, -529511546023990580322318, -461203690114705381636692, -425631037294543564424388, -362598317549089182965522, -211910260873924434992278, 86628402730369410037126, 393235914511157386592560, 568130515715804529143894, 471530447581677728708930, -36346048638858908516428, -596791435100683734317482, -851098173943677885301432, -577405209534704842328898, -269966440104540718045830],
  [-76673465250416104966292, -75153572655658404050499, -70496811963639308254762, -60268293919660485292646, -48403948371292385685962, -36511324828844287579212, -26197972792627325664830, -17304238938550272854620, -9670469927524686882284, -3137012415463053755490, 2455786921725853613958, 5079935535492470366010, 2707440872288159914582, -6689689626434786052444, -25139448504226860669084, -42615630309832132186310, -49092029571998381950958, -34542440839469678214000, 11059341354007125951694, 72901819529546537922982, 136173496218261208528790, 186062873946264716872010, 207758455224673426877432, 183417497819219487480064, 95197259475638760710778, -74745002050334747947486, -344252029007966104737822, -592807371378557182549546, -699894579153407997724042, -544997202308821351424592, -7598790831098188266546, 529575965926906008257000, 683802378612335754652950, 276171298119002296503122, -119043862592378359332768],
  [22201687984825218632080, 55815635745494394772748, 99604506347196359854478, 115169677751922778061970, 100815654869914581777734, 76741377904765078336094, 63145787065066646797408, 56610721051686444970774, 53718018615482347925630, 51049518462320585197108, 45187059328061816676544, 37338392901179926266432, 28711270885146013047368, 20513444988430247825982, 13952666904505586230802, 8876250075627062868440, 5131507954047855797576, 2565753977023927898788, 1026301591809385504722, -23176573319081796555328, -93732594863137500000000, -234331487157843750000000, -468662974315687500000000, -725723171885948037158052, -934508195422903720358242, -1024014160465835693306554, -923237182579020458339142, -742435279901855482724722, -591866470593734520636146, -581788772804053182794198, -822460204687206151645696, -1164720833536808569059926, -1459410726656473720358242, -1524716876440370000000000, -1499721517810200000000000],
  [0, -36043913437123145129554, -95635604704634362961828, -148668329581808864276726, -166479837241002075457168, -150203722485825495939194, -100973580119890625158844, -51184879797173495269104, -33233091161651994970892, -79513683862303084691160, -222422127543104653130826, -404352306061555345265626, -567698103270154734345262, -654853403021402393619436, -608212089167797896337850, -476681829750297242482260, -309170292819854575486490, -154585146412426823606262, -61834058563970915097298, -15458514639742960842816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 43748853432460800994450, 111235551256989097730234, 160243825476457523633038, 164841581802454113797582, 132840074873828266864580, 72050559314432166296644, 22899469299324191928098, 25813239023559010497402, 121218302647197786660778, 349541094360296115430652, 627387821935030360007616, 871364693138577811866228, 998077915748113905933114, 924133697535815005408866, 723129547414175858420708, 468662974315687500000000, 234331487157843750000000, 93732594863137500000000, 23433148715784375000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [-27877367487057005277302, -60284824767559451044285, -101601299644112100986222, -114092513699726395022294, -98112050275270836902684, -74671730151140023280052, -64783374102729479081024, -66716081244756365759994, -78738950716933203401526, -99121081638976225186048, -126131573155597022924158, -164616232172461793965552, -219420865600235807385960, -295391280354583403987146, -397373283361167068022942, -497458782558153572594142, -567739685913704121157744, -580307901375983630266610, -507255336908154231651704, -384445550257454978860156, -247742099171124925439096, -133008541406401268387722, -76108434710523061253164, -59033018307083901310714, -63773531404680170657562, -72321213216907323116932, -66667302972358027690150, -89540005267027701798818, -183667524711908978042640, -391778065917994489021320, -756599833491277795608528, -1154595685463135698902132, -1462228479864945000000000, -1524716876440370000000000, -1499721517810200000000000],
  [84181106714473474131049, 76906605013864251197066, 66368405654382001346974, 58738092836578428323116, 55429340411391946638706, 52586722550019845881912, 46354813403663128736766, 37130875154998167027728, 25312169951707830497020, 11295959961471275791000, -4520492648032340443974, -11239744765029914254682, 2035646742247945216232, 46203124995572485374056, 132160133106716810172010, 228328211841638631435592, 303128901946299374086164, 324983744166660463045088, 262314279263680538411828, 152004322288767382597448, 30937688308325993191114, -64001807621236775670076, -95930350428516854670922, -75887236484659550465924, -14911762155811097983548, 75956776201880411299808, 185679082217269670729644, 251958453504378095850498, 212498187687225245658976, 5001582359836248795480, -432828064848770264017350, -805085925169439714884698, -815867169838016597637782, -384800370006235803284474, -10385924555279070973148]
]
def hstarDen : ℤ := 50000000000000000000000000

def zRep (i j l : ℕ) : ℤ :=
  match hstarRPos i j with
  | some k => (hstarZStored.getD k []).getD l 0
  | none => 0

def zN (i j l : ℕ) : ℤ :=
  if 6 * i + j ≤ 17 then zRep i j l else zRep (5 - i) (5 - j) l

theorem Z_eq : ∀ i < 6, ∀ j < 6, ∀ l < 35, hstarRRep i j l * (hstarDen : ℚ) = zRep i j l := by
  decide +kernel

lemma hstarR_eq (i j : Fin 6) (l : Fin 35) :
    ((hstarR i j l : ℚ) : ℝ) = ((zN i j l : ℤ) : ℝ) / (hstarDen : ℝ) := by
  have hD : (hstarDen : ℝ) ≠ 0 := by norm_num [hstarDen]
  have key : hstarR i j l * (hstarDen : ℚ) = zN i j l := by
    unfold hstarR zN
    split_ifs
    · exact Z_eq i i.2 j j.2 l l.2
    · exact Z_eq _ (by omega) _ (by omega) l l.2
  rw [eq_div_iff hD]
  exact_mod_cast key

def sum6 (f : ℕ → ℤ) : ℤ := f 0 + f 1 + f 2 + f 3 + f 4 + f 5

def CN (ha hb l m n : ℕ) : ℤ :=
  sum6 fun i => sum6 fun j => zN i j l * LN ha i m * LN hb j n

theorem CN_bound : ∀ ha < 2, ∀ hb < 2, ∀ l < 35, ∀ m < 6, ∀ n < 6,
    |CN ha hb l m n| * 50 ≤ 1024 * hstarDen := by
  decide +kernel

lemma sum6_eq (f : ℕ → ℤ) : ((sum6 f : ℤ) : ℝ) = ∑ i : Fin 6, ((f i : ℤ) : ℝ) := by
  simp [sum6, Fin.sum_univ_six]

lemma comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    ∑ i, ∑ m, ∑ n, F i m n = ∑ m, ∑ n, ∑ i, F i m n := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]

lemma swap4 (F : Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℝ) :
    ∑ i, ∑ j, ∑ m, ∑ n, F i j m n = ∑ m, ∑ n, ∑ i, ∑ j, F i j m n := by
  rw [← comm3 (fun i m n => ∑ j, F i j m n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact comm3 (fun j m n => F i j m n)

/-- The `B`-polynomial part `R_l(a, b) = Σ_{i,j} R_{ijl} 𝓑⁵ᵢ(a) 𝓑⁵ⱼ(b)`. -/
noncomputable def Rl (l : Fin 35) (a b : ℝ) : ℝ :=
  ∑ i : Fin 6, ∑ j : Fin 6, ((hstarR i j l : ℚ) : ℝ) * DelaunayStretch.bernstein 5 i a * DelaunayStretch.bernstein 5 j b

lemma Rl_subdiv (l : Fin 35) (ha hb : ℕ) (hha : ha < 2) (hhb : hb < 2) (s t : ℝ) :
    Rl l (((ha : ℝ) + s) / 2) (((hb : ℝ) + t) / 2) =
      ∑ m : Fin 6, ∑ n : Fin 6, ((CN ha hb l m n : ℤ) : ℝ) / (1024 * (hstarDen : ℝ)) *
        DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t := by
  unfold Rl
  simp only [bernstein_subdiv ha hha, bernstein_subdiv hb hhb, hstarR_eq]
  have e : ∀ m n : Fin 6, ((CN ha hb l m n : ℤ) : ℝ) / (1024 * (hstarDen : ℝ)) *
        DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t =
      ∑ i : Fin 6, ∑ j : Fin 6, ((zN i j l : ℤ) : ℝ) / (hstarDen : ℝ) *
        (((LN ha i m : ℤ) : ℝ) / 32 * DelaunayStretch.bernstein 5 m s) *
        (((LN hb j n : ℤ) : ℝ) / 32 * DelaunayStretch.bernstein 5 n t) := by
    intro m n
    rw [CN, sum6_eq]
    simp only [sum6_eq, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  simp only [e]
  rw [← swap4]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma bound_of_coeffs (C : Fin 6 → Fin 6 → ℝ) (hC : ∀ m n, |C m n| ≤ 1 / 50) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |∑ m : Fin 6, ∑ n : Fin 6, C m n * DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t| ≤ 1 / 50 := by
  have hB : ∀ m n : Fin 6, 0 ≤ DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t := fun m n =>
    mul_nonneg (bernstein_nonneg' _ _ _ hs0 hs1) (bernstein_nonneg' _ _ _ ht0 ht1)
  calc |∑ m : Fin 6, ∑ n : Fin 6, C m n * DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t|
      ≤ ∑ m : Fin 6, |∑ n : Fin 6, C m n * DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 6, ∑ n : Fin 6, |C m n * DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t| :=
        Finset.sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m : Fin 6, ∑ n : Fin 6, 1 / 50 * (DelaunayStretch.bernstein 5 m s * DelaunayStretch.bernstein 5 n t) := by
        refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
        rw [mul_assoc, abs_mul, abs_of_nonneg (hB m n)]
        exact mul_le_mul_of_nonneg_right (hC m n) (hB m n)
    _ = 1 / 50 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul, bernstein5_sum]
        norm_num

lemma Rl_bound (l : Fin 35) (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |Rl l a b| ≤ 1 / 50 := by
  have half : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∃ h : ℕ, h < 2 ∧ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = ((h : ℝ) + s) / 2 := by
    intro x h0 h1
    by_cases hx : x ≤ 1 / 2
    · exact ⟨0, by norm_num, 2 * x, by linarith, by linarith, by push_cast; ring⟩
    · exact ⟨1, by norm_num, 2 * x - 1, by linarith, by linarith, by push_cast; ring⟩
  obtain ⟨ha, hha, s, hs0, hs1, rfl⟩ := half a ha0 ha1
  obtain ⟨hb, hhb, t, ht0, ht1, rfl⟩ := half b hb0 hb1
  rw [Rl_subdiv l ha hb hha hhb s t]
  apply bound_of_coeffs _ _ s t hs0 hs1 ht0 ht1
  intro m n
  have hD : (0 : ℝ) < hstarDen := by norm_num [hstarDen]
  have hc := CN_bound ha hha hb hhb l l.2 m m.2 n n.2
  have hc' : |((CN ha hb l m n : ℤ) : ℝ)| * 50 ≤ 1024 * (hstarDen : ℝ) := by exact_mod_cast hc
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1024 * hstarDen), div_le_iff₀ (by positivity)]
  linarith

lemma familyR_eq (γ a b : ℝ) :
    familyR hstarR γ a b = ∑ l : Fin 35, bspline l (2 * γ / Real.pi) * Rl l a b := by
  unfold familyR Rl
  simp only [Finset.mul_sum]
  rw [← comm3]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end CheckA

open CheckA in
theorem solution : ∀ γ a b : ℝ, 0 ≤ γ → γ ≤ Real.pi / 2 → 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
    |familyR hstarR γ a b| ≤ 1 / 50 := by
  intro γ a b hγ0 hγ1 ha0 ha1 hb0 hb1
  have hτ0 : 0 ≤ 2 * γ / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
  have hτ1 : 2 * γ / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]; linarith
  rw [familyR_eq]
  calc |∑ l : Fin 35, bspline l (2 * γ / Real.pi) * Rl l a b|
      ≤ ∑ l : Fin 35, |bspline l (2 * γ / Real.pi) * Rl l a b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin 35, bspline l (2 * γ / Real.pi) * (1 / 50) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (bspline_nonneg l _ hτ0 hτ1)]
        exact mul_le_mul_of_nonneg_left (Rl_bound l a b ha0 ha1 hb0 hb1)
          (bspline_nonneg l _ hτ0 hτ1)
    _ = 1 / 50 := by rw [← Finset.sum_mul, bspline_sum_one _ hτ0 hτ1]; ring
