-- Prove2me | solution 1 for CirclePackingConstants.six_unit_square_close_pair
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-09-24T19:50:39.782982+00:00
-- url     : https://prove2.me/submissions/c43eed11-f042-4071-9f74-3e6216fb127e

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem six_cp_sep_lo {a b s t : ℝ} (h : 13/36 < a^2 + b^2) (hst : s^2 + t^2 ≤ 13/36)
    (hb1 : b ≤ t) (hb2 : -t ≤ b) (ha : a ≤ s) : a < -s := by
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg (sub_nonneg.2 ha) (show 0 ≤ a + s by linarith),
    mul_nonneg (sub_nonneg.2 hb1) (show 0 ≤ b + t by linarith)]

theorem six_cp_sep_hi {a b s t : ℝ} (h : 13/36 < a^2 + b^2) (hst : s^2 + t^2 ≤ 13/36)
    (hb1 : b ≤ t) (hb2 : -t ≤ b) (ha : -s ≤ a) : s < a := by
  by_contra hc
  push_neg at hc
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (show 0 ≤ a + s by linarith),
    mul_nonneg (sub_nonneg.2 hb1) (show 0 ≤ b + t by linarith)]

theorem six_cp_sepy_lo {a b s t : ℝ} (h : 13/36 < b^2 + a^2) (hst : s^2 + t^2 ≤ 13/36)
    (hb1 : b ≤ t) (hb2 : -t ≤ b) (ha : a ≤ s) : a < -s :=
  six_cp_sep_lo (by linarith) hst hb1 hb2 ha

theorem six_cp_sepy_hi {a b s t : ℝ} (h : 13/36 < b^2 + a^2) (hst : s^2 + t^2 ≤ 13/36)
    (hb1 : b ≤ t) (hb2 : -t ≤ b) (ha : -s ≤ a) : s < a :=
  six_cp_sep_hi (by linarith) hst hb1 hb2 ha

theorem six_cp_redA (u v G B E F H : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (hv0 : 1/3 ≤ v)
    (hv1 : v ≤ 1/2) (hG0 : 1/2 ≤ G) (hG1 : G ≤ 1) (hB0 : 1/2 ≤ B) (hB1 : B ≤ 1) (hE0 : 1/2 ≤ E)
    (hE1 : E ≤ 2/3) (hF0 : 2/3 ≤ F) (hF1 : F ≤ 1) (hH0 : 2/3 ≤ H) (hH1 : H ≤ 1) (hGu : u ≤ G)
    (hBu : u ≤ B)
    (qac : 13/36 < u^2 + v^2) (qcf : 13/36 < u^2 + (F-v)^2) (qcg : 13/36 < (G-u)^2 + (H-v)^2)
    (qcb : 13/36 < (B-u)^2 + v^2) (qge : 13/36 < (1-G)^2 + (H-E)^2) (qbe : 13/36 < (1-B)^2 + E^2)
    (qfg : 13/36 < G^2 + (F-H)^2) (qce : 13/36 < (1-u)^2 + (E-v)^2) : False := by
  rcases le_total u (1/3:ℝ) with h0 | h0
  · exact absurd (show (0:ℝ) < 0 by
        linear_combination qac +
          (5/6) * hv1 +
          (1/3) * h0 +
          mul_nonneg (sub_nonneg.2 hu0) (sub_nonneg.2 h0) +
          mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1)) (lt_irrefl 0)
  · rcases le_total G (2/3:ℝ) with h1 | h1
    · rcases le_total B (2/3:ℝ) with h2 | h2
      · exact absurd (show (0:ℝ) < 0 by
            linear_combination (1/4) * qac +
              (3/4) * qcb +
              (5/6) * hv1 +
              (1/4) * h2 +
              (1/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h2) +
              mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hBu) +
              mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
              (3/4) * mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hBu)) (lt_irrefl 0)
      · rcases le_total B (5/6:ℝ) with h3 | h3
        · rcases le_total F (5/6:ℝ) with h4 | h4
          · exact absurd (show (0:ℝ) < 0 by
                linear_combination (1/2) * qcf +
                  (1/2) * qcb +
                  (1/6) * h3 +
                  (1/4) * h4 +
                  mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hu1) +
                  (1/2) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h3) +
                  mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                  mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 h4) +
                  (1/2) * mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hBu) +
                  (1/2) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4)) (lt_irrefl 0)
          · rcases le_total H (5/6:ℝ) with h5 | h5
            · exact absurd (show (0:ℝ) < 0 by
                  linear_combination (7/20) * qac +
                    (3/10) * qcg +
                    (1/10) * qge +
                    (1/4) * qce +
                    (1/10) * hv1 +
                    (13/120) * hE1 +
                    (3/10) * h5 +
                    (7/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1) +
                    (9/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                    (9/10) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                    (1/2) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hE0) +
                    (3/5) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hGu) +
                    (7/20) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                    (1/5) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 h5)) (lt_irrefl 0)
            · rcases le_total u (5/12:ℝ) with h6 | h6
              · rcases le_total v (5/12:ℝ) with h7 | h7
                · exact absurd (show (0:ℝ) < 0 by
                      linear_combination qac +
                        (1/6) * hv1 +
                        (3/4) * h6 +
                        (7/12) * h7 +
                        mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                        mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7)) (lt_irrefl 0)
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (13/24) * qac +
                          (11/24) * qcg +
                          (55/144) * hH1 +
                          (77/288) * h6 +
                          (1/24) * h8 +
                          (11/16) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                          (5/16) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                          mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (11/12) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (7/48) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h3) +
                          (11/24) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                          (7/48) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hBu) +
                          (11/24) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (91/298) * qac +
                          (189/596) * qcg +
                          (45/596) * qcb +
                          (105/596) * qge +
                          (75/596) * qbe +
                          (5/894) * hv1 +
                          (105/298) * hH1 +
                          (104/149) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                          (45/298) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h2) +
                          (189/298) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h1) +
                          (104/149) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (189/298) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (147/298) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (30/149) * mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3) +
                          (45/149) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (105/298) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (147/298) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
              · rcases le_total v (5/12:ℝ) with h7 | h7
                · exact absurd (show (0:ℝ) < 0 by
                      linear_combination (47/177) * qac +
                        (39/59) * qcb +
                        (13/177) * qbe +
                        (91/1062) * hE1 +
                        (44/177) * h3 +
                        (41/59) * h7 +
                        (164/177) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hBu) +
                        (20/59) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h2) +
                        (164/177) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                        (130/177) * mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hBu) +
                        (13/177) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1)) (lt_irrefl 0)
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · linarith only [qac, qcf, qcg, qcb, qge, qbe, qfg, qce, hu0, hu1, hv0, hv1, hG0, hG1, hB0, hB1, hE0, hE1, hF0, hF1, hH0, hH1, hGu, hBu, h0, h1, h2, h3, h4, h5, h6, h7, h8,
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h2),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu),
                        mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hG0),
                        mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1),
                        mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu),
                        mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hBu),
                        mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1),
                        mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h5),
                        mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 hH1) (sub_nonneg.2 hBu)]
                  · linarith only [qac, qcf, qcg, qcb, qge, qbe, qfg, qce, hu0, hu1, hv0, hv1, hG0, hG1, hB0, hB1, hE0, hE1, hF0, hF1, hH0, hH1, hGu, hBu, h0, h1, h2, h3, h4, h5, h6, h7, h8,
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hBu),
                        mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1),
                        mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE0),
                        mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1),
                        mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hGu),
                        mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3),
                        mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1),
                        mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 hH1) (sub_nonneg.2 hH1)]
        · rcases le_total F (5/6:ℝ) with h4 | h4
          · rcases le_total H (5/6:ℝ) with h5 | h5
            · exact absurd (show (0:ℝ) < 0 by
                  linear_combination (7/20) * qac +
                    (3/10) * qcg +
                    (1/10) * qge +
                    (1/4) * qce +
                    (1/10) * hv1 +
                    (13/120) * hE1 +
                    (3/10) * h5 +
                    (7/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1) +
                    (9/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                    (9/10) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                    (1/2) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hE0) +
                    (3/5) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hGu) +
                    (7/20) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                    (1/5) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 h5)) (lt_irrefl 0)
            · rcases le_total u (5/12:ℝ) with h6 | h6
              · exact absurd (show (0:ℝ) < 0 by
                    linear_combination (11/20) * qac +
                      (9/20) * qcf +
                      (1/12) * hv1 +
                      (9/40) * h4 +
                      (3/4) * h6 +
                      mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                      mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                      (9/10) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 h4) +
                      (9/20) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4)) (lt_irrefl 0)
              · rcases le_total v (5/12:ℝ) with h7 | h7
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · rcases le_total B (11/12:ℝ) with h9 | h9
                    · rcases le_total E (7/12:ℝ) with h10 | h10
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (4/7) * qac +
                              (3/7) * qce +
                              (5/84) * hu1 +
                              (1/4) * h7 +
                              (3/28) * h10 +
                              mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                              mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                              (6/7) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 h10) +
                              (3/7) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h10)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (169/616) * qac +
                              (3/28) * qcf +
                              (5/77) * qcb +
                              (1/7) * qge +
                              (1/7) * qfg +
                              (15/56) * qce +
                              (1/224) * hE1 +
                              (2/21) * hH1 +
                              (25/924) * h9 +
                              (5/7) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                              (2/7) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h8) +
                              (5/77) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h9) +
                              (5/7) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                              (15/28) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE1) +
                              (3/14) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 h4) +
                              (2/7) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                              (5/77) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hBu) +
                              (23/56) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hE1) +
                              (2/7) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (1/4) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4) +
                              (2/7) * mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hH1) +
                              (2/7) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                    · rcases le_total E (7/12:ℝ) with h10 | h10
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination qbe +
                              (1/6) * hE1 +
                              (1/12) * h9 +
                              (11/12) * h10 +
                              mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hB1) +
                              mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h10)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (49/162) * qac +
                              (55/648) * qcf +
                              (325/1944) * qge +
                              (275/1944) * qfg +
                              (197/648) * qce +
                              (5/3888) * hE1 +
                              (625/5832) * hH1 +
                              (56/81) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                              (25/81) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hG0) +
                              (56/81) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                              (55/324) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hF0) +
                              (197/324) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE1) +
                              (25/81) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                              (229/486) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hE1) +
                              (325/972) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (55/243) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4) +
                              (275/972) * mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hH1) +
                              (25/81) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (11/26) * qac +
                          (2/13) * qge +
                          (11/26) * qce +
                          (1/78) * hE1 +
                          (1/13) * hH1 +
                          (11/156) * h7 +
                          (7/156) * h8 +
                          (11/13) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu) +
                          (11/13) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h8) +
                          (11/13) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                          (11/13) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE1) +
                          (2/13) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (15/26) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (4/13) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (2/13) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (25/164) * qac +
                          (10/41) * qcf +
                          (11/82) * qge +
                          (11/82) * qfg +
                          (55/164) * qce +
                          (5/492) * hv1 +
                          (11/123) * hH1 +
                          (47/492) * h4 +
                          (30/41) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                          (11/41) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h8) +
                          (30/41) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (55/82) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE0) +
                          (20/41) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hF0) +
                          (11/41) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                          (77/164) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (11/41) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (31/82) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4) +
                          (11/41) * mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hH1) +
                          (11/41) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (1/6) * qac +
                          (1/4) * qcf +
                          (1/6) * qge +
                          (5/12) * qce +
                          (1/72) * hv1 +
                          (1/12) * hH1 +
                          (1/6) * h4 +
                          (1/18) * h8 +
                          (5/6) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu) +
                          (5/6) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h8) +
                          (5/6) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (5/6) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE0) +
                          (1/2) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hF0) +
                          (1/6) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (7/12) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (1/3) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (1/4) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h4) +
                          (1/6) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
          · rcases le_total H (5/6:ℝ) with h5 | h5
            · exact absurd (show (0:ℝ) < 0 by
                  linear_combination (7/20) * qac +
                    (3/10) * qcg +
                    (1/10) * qge +
                    (1/4) * qce +
                    (1/10) * hv1 +
                    (13/120) * hE1 +
                    (3/10) * h5 +
                    (7/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h1) +
                    (9/10) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                    (9/10) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                    (1/2) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hE0) +
                    (3/5) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hGu) +
                    (7/20) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                    (1/5) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
                    (2/5) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 h5)) (lt_irrefl 0)
            · rcases le_total u (5/12:ℝ) with h6 | h6
              · rcases le_total v (5/12:ℝ) with h7 | h7
                · exact absurd (show (0:ℝ) < 0 by
                      linear_combination qac +
                        (1/6) * hu1 +
                        (7/12) * h6 +
                        (3/4) * h7 +
                        mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                        mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7)) (lt_irrefl 0)
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (181/373) * qac +
                          (319/746) * qcg +
                          (15/746) * qcb +
                          (35/746) * qge +
                          (15/746) * qbe +
                          (295/746) * hH1 +
                          (719/4476) * h6 +
                          (109/4476) * h8 +
                          (348/373) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                          (142/373) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h8) +
                          (348/373) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (319/373) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (177/373) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                          (15/373) * mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hBu) +
                          (25/373) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (35/373) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h5) +
                          (177/373) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (13/84) * qac +
                          (11/84) * qcg +
                          (5/12) * qge +
                          (25/84) * qbe +
                          (20/63) * hH1 +
                          (25/504) * h3 +
                          (31/504) * h6 +
                          (17/72) * h8 +
                          (2/7) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h6) +
                          (11/42) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h8) +
                          (2/7) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (11/42) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (23/42) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (25/84) * mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hB1) +
                          (5/7) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (5/6) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (23/42) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
              · rcases le_total v (5/12:ℝ) with h7 | h7
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · linarith only [qac, qcf, qcg, qcb, qge, qbe, qfg, qce, hu0, hu1, hv0, hv1, hG0, hG1, hB0, hB1, hE0, hE1, hF0, hF1, hH0, hH1, hGu, hBu, h0, h1, h2, h3, h4, h5, h6, h7, h8,
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h8),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h4),
                        mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hG0),
                        mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7),
                        mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE1),
                        mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu),
                        mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 h4),
                        mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1),
                        mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hF1),
                        mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hBu),
                        mul_nonneg (sub_nonneg.2 hF1) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1),
                        mul_nonneg (sub_nonneg.2 hH1) (sub_nonneg.2 hBu)]
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (11/26) * qac +
                          (2/13) * qge +
                          (11/26) * qce +
                          (1/78) * hE1 +
                          (1/13) * hH1 +
                          (11/156) * h7 +
                          (7/156) * h8 +
                          (11/13) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu) +
                          (11/13) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h8) +
                          (11/13) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h7) +
                          (11/13) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE1) +
                          (2/13) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (15/26) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (4/13) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (2/13) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                · rcases le_total G (7/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (286/843) * qac +
                          (11/1124) * qcf +
                          (221/843) * qcg +
                          (53/562) * qge +
                          (33/562) * qfg +
                          (265/1124) * qce +
                          (647/2529) * hH1 +
                          (704/843) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                          (10/843) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu) +
                          (82/843) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h8) +
                          (238/281) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (265/562) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE0) +
                          (11/562) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 h4) +
                          (442/843) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (350/843) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                          (371/1124) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (53/281) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (77/1124) * mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hF1) +
                          (33/281) * mul_nonneg (sub_nonneg.2 hF1) (sub_nonneg.2 hH1) +
                          (350/843) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (134/417) * qac +
                          (36/139) * qcg +
                          (5/834) * qcb +
                          (20/139) * qge +
                          (5/139) * qbe +
                          (65/278) * qce +
                          (40/139) * hH1 +
                          (202/417) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hu1) +
                          (76/417) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h8) +
                          (5/417) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 h3) +
                          (140/417) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hGu) +
                          (114/139) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hv1) +
                          (65/139) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hE0) +
                          (72/139) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                          (56/139) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                          (35/834) * mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hB1) +
                          (115/278) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (40/139) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                          (56/139) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1)) (lt_irrefl 0)
    · exact absurd (show (0:ℝ) < 0 by
          linear_combination qge +
            (1/6) * hE0 +
            (2/3) * hH1 +
            (1/3) * h1 +
            mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hG1) +
            mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
            2 * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
            mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 hH1)) (lt_irrefl 0)

theorem six_cp_redB (u v G B E F H M : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (hv0 : 1/3 ≤ v)
    (hv1 : v ≤ 1/2) (hG0 : 1/2 ≤ G) (hG1 : G ≤ 1) (hB0 : 1/2 ≤ B) (hB1 : B ≤ 1) (hE0 : 1/2 ≤ E)
    (hE1 : E ≤ 2/3) (hF0 : 2/3 ≤ F) (hF1 : F ≤ 1) (hH0 : 2/3 ≤ H) (hH1 : H ≤ 1) (hGu : u ≤ G)
    (hBu : u ≤ B) (hM0 : 1/2 ≤ M) (hM1 : M ≤ 1) (hBM : M ≤ B) (hMG : G + 1/3 ≤ M)
    (qac : 13/36 < u^2 + v^2) (qcf : 13/36 < u^2 + (F-v)^2) (qcg : 13/36 < (G-u)^2 + (H-v)^2)
    (qcb : 13/36 < (B-u)^2 + v^2) (qge : 13/36 < (1-G)^2 + (H-E)^2) (qbe : 13/36 < (1-M)^2 + E^2)
    (qfg : 13/36 < G^2 + (F-H)^2) (qce : 13/36 < (1-u)^2 + (E-v)^2) : False := by
  rcases le_total u (1/3:ℝ) with h0 | h0
  · exact absurd (show (0:ℝ) < 0 by
        linear_combination qac +
          (5/6) * hv1 +
          (1/3) * h0 +
          mul_nonneg (sub_nonneg.2 hu0) (sub_nonneg.2 h0) +
          mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1)) (lt_irrefl 0)
  · rcases le_total G (2/3:ℝ) with h1 | h1
    · rcases le_total B (2/3:ℝ) with h2 | h2
      · exact absurd (show (0:ℝ) < 0 by
            linear_combination (1/4) * qac +
              (3/4) * qcb +
              (5/6) * hv1 +
              (1/4) * h2 +
              (1/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h2) +
              mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hBu) +
              mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
              (3/4) * mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hBu)) (lt_irrefl 0)
      · rcases le_total M (3/4:ℝ) with h3 | h3
        · exact absurd (show (0:ℝ) < 0 by
              linear_combination (3/8) * qac +
                (5/8) * qce +
                (11/12) * hG0 +
                (5/48) * hE1 +
                (1/12) * hGu +
                hMG +
                h3 +
                mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hB1) +
                mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hBu) +
                mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                (5/4) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hE1) +
                (5/8) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1)) (lt_irrefl 0)
        · rcases le_total B (5/6:ℝ) with h4 | h4
          · exact absurd (show (0:ℝ) < 0 by
                linear_combination (1/3) * qac +
                  (5/12) * qcg +
                  (1/4) * qcb +
                  (5/18) * hH1 +
                  (5/24) * hBM +
                  (5/24) * hMG +
                  (1/3) * h4 +
                  (1/12) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hG0) +
                  mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                  (1/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hBM) +
                  (1/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hMG) +
                  mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                  (5/6) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                  (5/12) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                  (5/12) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                  (1/4) * mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hBu) +
                  (5/12) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 hH1)) (lt_irrefl 0)
          · rcases le_total F (5/6:ℝ) with h5 | h5
            · rcases le_total H (5/6:ℝ) with h6 | h6
              · exact absurd (show (0:ℝ) < 0 by
                    linear_combination (9/17) * qac +
                      (8/17) * qcg +
                      (20/51) * hu1 +
                      (5/102) * hv1 +
                      (4/51) * hM1 +
                      (8/51) * h1 +
                      (4/17) * h6 +
                      (1/17) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hB1) +
                      (16/17) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hGu) +
                      (1/17) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hBu) +
                      (8/17) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hMG) +
                      mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                      (16/17) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 h6) +
                      (8/17) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                      (8/17) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 h6) +
                      (8/17) * mul_nonneg (sub_nonneg.2 hGu) (sub_nonneg.2 hMG)) (lt_irrefl 0)
              · rcases le_total M (7/8:ℝ) with h7 | h7
                · rcases le_total u (5/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (19/40) * qac +
                          (2/5) * qcf +
                          (1/8) * qce +
                          (1/48) * hE1 +
                          (1/5) * h5 +
                          (1/2) * h8 +
                          mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h8) +
                          mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                          (1/4) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hE1) +
                          (4/5) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 h5) +
                          (1/8) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (2/5) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5)) (lt_irrefl 0)
                  · rcases le_total v (5/12:ℝ) with h9 | h9
                    · rcases le_total G (7/12:ℝ) with h10 | h10
                      · rcases le_total B (11/12:ℝ) with h11 | h11
                        · exact absurd (show (0:ℝ) < 0 by
                              linear_combination (793/2584) * qac +
                                (125/1292) * qcf +
                                (15/323) * qcb +
                                (115/969) * qge +
                                (125/969) * qfg +
                                (781/2584) * qce +
                                (43/23256) * hE1 +
                                (235/2907) * hH1 +
                                (20/969) * hMG +
                                (10/323) * h11 +
                                (243/323) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                (80/323) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h7) +
                                (30/323) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h11) +
                                (243/323) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                (781/1292) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                                (125/646) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h5) +
                                (80/323) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                                (15/323) * mul_nonneg (sub_nonneg.2 h11) (sub_nonneg.2 h3) +
                                (15/323) * mul_nonneg (sub_nonneg.2 h11) (sub_nonneg.2 hBM) +
                                (3263/7752) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                                (230/969) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                                (875/3876) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                                (250/969) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                                (80/323) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                                (80/323) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hGu)) (lt_irrefl 0)
                        · rcases le_total E (7/12:ℝ) with h12 | h12
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination (4/7) * qac +
                                  (3/7) * qce +
                                  (5/84) * hu1 +
                                  (1/4) * h9 +
                                  (3/28) * h12 +
                                  mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                  mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                  (6/7) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h12) +
                                  (3/7) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h12)) (lt_irrefl 0)
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination (483/1504) * qac +
                                  (115/1504) * qcf +
                                  (625/4512) * qge +
                                  (575/4512) * qfg +
                                  (253/752) * qce +
                                  (655/18048) * hE1 +
                                  (1225/13536) * hH1 +
                                  (69/94) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                  (69/94) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                  (115/752) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hF0) +
                                  (253/376) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                                  (25/94) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 h7) +
                                  (25/94) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                                  (2143/4512) * mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hE1) +
                                  (625/2256) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                                  (115/564) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                                  (575/2256) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                                  (25/94) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (13/24) * qac +
                              (11/24) * qce +
                              (11/72) * hE1 +
                              (5/18) * hMG +
                              (5/18) * h7 +
                              (5/36) * h9 +
                              (5/18) * h10 +
                              mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                              (11/12) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                              (11/24) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1)) (lt_irrefl 0)
                    · exact absurd (show (0:ℝ) < 0 by
                          linear_combination (345/1424) * qac +
                            (253/1424) * qcf +
                            (20/89) * qfg +
                            (253/712) * qce +
                            (253/4272) * hE1 +
                            (10/267) * hH1 +
                            (125/534) * hMG +
                            (13/2136) * h5 +
                            (125/534) * h7 +
                            (69/89) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                            (69/89) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                            (253/712) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hF0) +
                            (253/356) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hE1) +
                            (20/89) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 h7) +
                            (20/89) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                            (253/712) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                            (573/1424) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                            (40/89) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                            (20/89) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                · rcases le_total u (5/12:ℝ) with h8 | h8
                  · exact absurd (show (0:ℝ) < 0 by
                        linear_combination (19/40) * qac +
                          (2/5) * qcf +
                          (1/8) * qce +
                          (1/48) * hE1 +
                          (1/5) * h5 +
                          (1/2) * h8 +
                          mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h8) +
                          mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                          (1/4) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hE1) +
                          (4/5) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 h5) +
                          (1/8) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                          (2/5) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5)) (lt_irrefl 0)
                  · rcases le_total v (5/12:ℝ) with h9 | h9
                    · rcases le_total G (7/12:ℝ) with h10 | h10
                      · rcases le_total B (11/12:ℝ) with h11 | h11
                        · rcases le_total E (7/12:ℝ) with h12 | h12
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination (4/7) * qac +
                                  (3/7) * qce +
                                  (5/84) * hu1 +
                                  (1/4) * h9 +
                                  (3/28) * h12 +
                                  mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                  mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                  (6/7) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h12) +
                                  (3/7) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h12)) (lt_irrefl 0)
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination (2003/8634) * qac +
                                  (333/2878) * qcf +
                                  (214/4317) * qcb +
                                  (847/4317) * qge +
                                  (222/1439) * qfg +
                                  (363/1439) * qce +
                                  (1069/8634) * hH1 +
                                  (83/8634) * hBM +
                                  (35/25902) * h11 +
                                  (2804/4317) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                  (2804/4317) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                  (726/1439) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h12) +
                                  (333/1439) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h5) +
                                  (1015/4317) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                                  (1513/4317) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                                  (712/4317) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 h7) +
                                  (428/4317) * mul_nonneg (sub_nonneg.2 h11) (sub_nonneg.2 hM1) +
                                  (428/4317) * mul_nonneg (sub_nonneg.2 h11) (sub_nonneg.2 hBu) +
                                  (214/4317) * mul_nonneg (sub_nonneg.2 h11) (sub_nonneg.2 hMG) +
                                  (1936/4317) * mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hE1) +
                                  (1694/4317) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                                  (777/2878) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                                  (444/1439) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                                  (1513/4317) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                                  (214/4317) * mul_nonneg (sub_nonneg.2 hBM) (sub_nonneg.2 hBM) +
                                  (214/4317) * mul_nonneg (sub_nonneg.2 hBM) (sub_nonneg.2 hMG)) (lt_irrefl 0)
                        · rcases le_total E (7/12:ℝ) with h12 | h12
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination qbe +
                                  (1/6) * h7 +
                                  (13/12) * h12 +
                                  mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                                  mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 h12) +
                                  mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 hMG)) (lt_irrefl 0)
                          · exact absurd (show (0:ℝ) < 0 by
                                linear_combination (21/68) * qac +
                                  (5/68) * qcf +
                                  (35/204) * qge +
                                  (25/204) * qfg +
                                  (11/34) * qce +
                                  (5/816) * hE1 +
                                  (65/612) * hH1 +
                                  (12/17) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                                  (12/17) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                                  (5/34) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hF0) +
                                  (11/17) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                                  (5/17) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                                  (5/17) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                                  (101/204) * mul_nonneg (sub_nonneg.2 h12) (sub_nonneg.2 hE1) +
                                  (35/102) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                                  (10/51) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                                  (25/102) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                                  (5/17) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (143/304) * qac +
                              (5/38) * qge +
                              (121/304) * qce +
                              (7/304) * hE1 +
                              (5/76) * hH1 +
                              (55/456) * h9 +
                              (15/152) * h10 +
                              (33/38) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              (33/38) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                              (121/152) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hM1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hMG) +
                              (161/304) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                    · rcases le_total G (7/12:ℝ) with h10 | h10
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (87/608) * qac +
                              (149/608) * qcf +
                              (5/38) * qge +
                              (5/38) * qfg +
                              (53/152) * qce +
                              (1/152) * hE1 +
                              (5/57) * hH1 +
                              (89/912) * h5 +
                              (14/19) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hM1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hMG) +
                              (14/19) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                              (53/76) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE0) +
                              (149/304) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hF0) +
                              (5/19) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hGu) +
                              (73/152) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (229/608) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                              (5/19) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hH1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (179/1056) * qac +
                              (313/1056) * qcf +
                              (5/33) * qge +
                              (101/264) * qce +
                              (1/792) * hE1 +
                              (5/66) * hH1 +
                              (5/396) * hMG +
                              (313/1584) * h5 +
                              (25/198) * h10 +
                              (28/33) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              (5/33) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 h10) +
                              (5/33) * mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hMG) +
                              (28/33) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                              (101/132) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE0) +
                              (313/528) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hF0) +
                              (5/33) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hMG) +
                              (47/88) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (10/33) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (313/1056) * mul_nonneg (sub_nonneg.2 hF0) (sub_nonneg.2 h5) +
                              (5/33) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                              (5/33) * mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 hGu)) (lt_irrefl 0)
            · rcases le_total H (5/6:ℝ) with h6 | h6
              · exact absurd (show (0:ℝ) < 0 by
                    linear_combination (123/268) * qac +
                      (105/268) * qcg +
                      (35/268) * qge +
                      (5/268) * qbe +
                      (85/268) * hu1 +
                      (25/134) * hv1 +
                      (45/536) * hM1 +
                      (105/268) * h6 +
                      (57/67) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hu1) +
                      (105/134) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hG0) +
                      (35/67) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hMG) +
                      (57/67) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hv1) +
                      (105/134) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 hH0) +
                      (145/268) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                      (5/268) * mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hMG) +
                      (10/67) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                      (35/134) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
                      (35/67) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 h6) +
                      (35/67) * mul_nonneg (sub_nonneg.2 hGu) (sub_nonneg.2 hMG) +
                      (5/268) * mul_nonneg (sub_nonneg.2 hBM) (sub_nonneg.2 hMG)) (lt_irrefl 0)
              · rcases le_total M (7/8:ℝ) with h7 | h7
                · exact absurd (show (0:ℝ) < 0 by
                      linear_combination (49/208) * qge +
                        (35/208) * qbe +
                        (31/52) * qfg +
                        (31/312) * hF1 +
                        (271/1248) * hH1 +
                        (427/1664) * hMG +
                        (9/26) * h7 +
                        (173/208) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hMG) +
                        mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 h7) +
                        (21/52) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                        (49/104) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                        (31/52) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hF1) +
                        (31/26) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 h6) +
                        (173/208) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                        (35/208) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hMG) +
                        (173/208) * mul_nonneg (sub_nonneg.2 hGu) (sub_nonneg.2 hMG)) (lt_irrefl 0)
                · rcases le_total u (5/12:ℝ) with h8 | h8
                  · rcases le_total v (5/12:ℝ) with h9 | h9
                    · exact absurd (show (0:ℝ) < 0 by
                          linear_combination (3/4) * qac +
                            (1/4) * qce +
                            (1/12) * hE1 +
                            (1/4) * h8 +
                            (5/12) * h9 +
                            mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h8) +
                            mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                            (1/2) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                            (1/4) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1)) (lt_irrefl 0)
                    · exact absurd (show (0:ℝ) < 0 by
                          linear_combination (85/203) * qac +
                            (10/29) * qcg +
                            (4/29) * qge +
                            (20/203) * qbe +
                            (25/2436) * hv1 +
                            (31/87) * hH1 +
                            (5/406) * h7 +
                            (275/2436) * h8 +
                            (155/203) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h8) +
                            (20/29) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h1) +
                            (155/203) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                            (20/29) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hH1) +
                            (14/29) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 h1) +
                            (48/203) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                            (8/29) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                            (14/29) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                            (20/203) * mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 hM1)) (lt_irrefl 0)
                  · rcases le_total v (5/12:ℝ) with h9 | h9
                    · rcases le_total G (7/12:ℝ) with h10 | h10
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (14/37) * qge +
                              (10/37) * qbe +
                              (13/37) * qfg +
                              (29/222) * hH1 +
                              (13/222) * h5 +
                              (6/37) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 h10) +
                              (11/37) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hM1) +
                              (21/37) * mul_nonneg (sub_nonneg.2 hG0) (sub_nonneg.2 hMG) +
                              (20/37) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 h7) +
                              (6/37) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hGu) +
                              (24/37) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (28/37) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (13/37) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hF1) +
                              (26/37) * mul_nonneg (sub_nonneg.2 hF1) (sub_nonneg.2 hH1) +
                              (27/37) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                              (10/37) * mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 hMG)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (143/304) * qac +
                              (5/38) * qge +
                              (121/304) * qce +
                              (7/304) * hE1 +
                              (5/76) * hH1 +
                              (55/456) * h9 +
                              (15/152) * h10 +
                              (33/38) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              (33/38) * mul_nonneg (sub_nonneg.2 hv0) (sub_nonneg.2 h9) +
                              (121/152) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hM1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hMG) +
                              (161/304) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (5/19) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (5/38) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1)) (lt_irrefl 0)
                    · rcases le_total G (7/12:ℝ) with h10 | h10
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (868/3377) * qac +
                              (1003/3377) * qcg +
                              (1845/13508) * qge +
                              (743/13508) * qbe +
                              (356/3377) * qfg +
                              (503/3377) * qce +
                              (3/6754) * hv1 +
                              (9869/27016) * hH1 +
                              (743/162096) * hMG +
                              (2374/3377) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hu1) +
                              (2374/3377) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                              (1006/3377) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hE0) +
                              (2006/3377) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h6) +
                              (2006/3377) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hGu) +
                              (743/13508) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hMG) +
                              (1150/3377) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (1845/6754) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (356/3377) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 hF1) +
                              (356/3377) * mul_nonneg (sub_nonneg.2 h5) (sub_nonneg.2 h6) +
                              (356/3377) * mul_nonneg (sub_nonneg.2 hF1) (sub_nonneg.2 hH1) +
                              (7281/13508) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                              (743/13508) * mul_nonneg (sub_nonneg.2 hM1) (sub_nonneg.2 hMG)) (lt_irrefl 0)
                      · exact absurd (show (0:ℝ) < 0 by
                            linear_combination (1/6) * qac +
                              (2/7) * qcg +
                              (131/504) * qge +
                              (85/504) * qbe +
                              (5/42) * qce +
                              (419/1008) * hH1 +
                              (85/6048) * hMG +
                              (1/9) * h9 +
                              (17/189) * h10 +
                              (4/7) * mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hGu) +
                              (4/7) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 hv1) +
                              (4/7) * mul_nonneg (sub_nonneg.2 h9) (sub_nonneg.2 h6) +
                              (5/21) * mul_nonneg (sub_nonneg.2 hv1) (sub_nonneg.2 hE1) +
                              (5/7) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hM1) +
                              (275/504) * mul_nonneg (sub_nonneg.2 h10) (sub_nonneg.2 hMG) +
                              (85/504) * mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hMG) +
                              (23/42) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
                              (131/252) * mul_nonneg (sub_nonneg.2 hE1) (sub_nonneg.2 hH1) +
                              (275/504) * mul_nonneg (sub_nonneg.2 h6) (sub_nonneg.2 hH1) +
                              (85/504) * mul_nonneg (sub_nonneg.2 hBM) (sub_nonneg.2 hMG)) (lt_irrefl 0)
    · exact absurd (show (0:ℝ) < 0 by
          linear_combination (3/4) * qge +
            (1/4) * qbe +
            (1/6) * hE1 +
            (1/2) * hH1 +
            (1/8) * hBM +
            (1/8) * hMG +
            (7/8) * h1 +
            (3/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hB1) +
            (3/4) * mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 hMG) +
            (3/4) * mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hBM) +
            (1/4) * mul_nonneg (sub_nonneg.2 hB0) (sub_nonneg.2 hM1) +
            (3/4) * mul_nonneg (sub_nonneg.2 hB1) (sub_nonneg.2 hGu) +
            mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hE1) +
            (3/2) * mul_nonneg (sub_nonneg.2 hE0) (sub_nonneg.2 hH0) +
            (3/4) * mul_nonneg (sub_nonneg.2 hH0) (sub_nonneg.2 hH1) +
            (1/4) * mul_nonneg (sub_nonneg.2 hM0) (sub_nonneg.2 hBM) +
            (3/4) * mul_nonneg (sub_nonneg.2 hGu) (sub_nonneg.2 hMG)) (lt_irrefl 0)

theorem six_cp_low (a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 : ℝ)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1/3)
    (hb1 : 1/2 ≤ b1) (hb1' : b1 ≤ 1) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 1/3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1/2) (hc2 : 1/3 ≤ c2) (hc2' : c2 ≤ 2/3)
    (he1 : 1/2 ≤ e1) (he1' : e1 ≤ 1) (he2 : 1/3 ≤ e2) (he2' : e2 ≤ 2/3)
    (hf1 : 0 ≤ f1) (hf1' : f1 ≤ 1/2) (hf2 : 2/3 ≤ f2) (hf2' : f2 ≤ 1)
    (hg1 : 1/2 ≤ g1) (hg1' : g1 ≤ 1) (hg2 : 2/3 ≤ g2) (hg2' : g2 ≤ 1)
    (hab : 13/36 < (a1 - b1)^2 + (a2 - b2)^2)
    (hac : 13/36 < (a1 - c1)^2 + (a2 - c2)^2)
    (hae : 13/36 < (a1 - e1)^2 + (a2 - e2)^2)
    (haf : 13/36 < (a1 - f1)^2 + (a2 - f2)^2)
    (hag : 13/36 < (a1 - g1)^2 + (a2 - g2)^2)
    (hbc : 13/36 < (b1 - c1)^2 + (b2 - c2)^2)
    (hbe : 13/36 < (b1 - e1)^2 + (b2 - e2)^2)
    (hbf : 13/36 < (b1 - f1)^2 + (b2 - f2)^2)
    (hbg : 13/36 < (b1 - g1)^2 + (b2 - g2)^2)
    (hce : 13/36 < (c1 - e1)^2 + (c2 - e2)^2)
    (hcf : 13/36 < (c1 - f1)^2 + (c2 - f2)^2)
    (hcg : 13/36 < (c1 - g1)^2 + (c2 - g2)^2)
    (hef : 13/36 < (e1 - f1)^2 + (e2 - f2)^2)
    (heg : 13/36 < (e1 - g1)^2 + (e2 - g2)^2)
    (hfg : 13/36 < (f1 - g1)^2 + (f2 - g2)^2)
    (hc : c2 ≤ 1/2) (he : e2 ≤ 1/2) : False := by
  have k1 : (1/3:ℝ)^2 + (1/2)^2 ≤ 13/36 := by norm_num
  rcases le_total a1 c1 with h1 | h1 <;> rcases le_total b1 e1 with h2 | h2
  · have t1 := six_cp_sep_lo hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [h1])
    have t2 := six_cp_sep_hi hbc k1 (by linarith only [hb2', hc2]) (by linarith only [hb2, hc]) (by linarith only [hb1, hc1'])
    have t3 := six_cp_sep_lo hbe k1 (by linarith only [hb2', he2]) (by linarith only [hb2, he]) (by linarith only [h2])
    linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, h1, h2, t1, t2, t3]
  · have t1 := six_cp_sep_lo hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [h1])
    have t2 := six_cp_sep_lo hce k1 (by linarith only [hc2', he2]) (by linarith only [hc2, he2']) (by linarith only [hc1', he1])
    have t3 := six_cp_sep_hi hbe k1 (by linarith only [hb2', he2]) (by linarith only [hb2, he]) (by linarith only [h2])
    linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, h1, h2, t1, t2, t3]
  · have t1 := six_cp_sep_hi hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [h1])
    have t2 := six_cp_sep_lo hab k1 (by linarith only [ha2', hb2]) (by linarith only [ha2, hb2']) (by linarith only [ha1', hb1])
    have t3 := six_cp_sep_lo hbe k1 (by linarith only [hb2', he2]) (by linarith only [hb2, he]) (by linarith only [h2])
    linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, h1, h2, t1, t2, t3]
  · have t1 := six_cp_sep_hi hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [h1])
    have t2 := six_cp_sep_lo hae k1 (by linarith only [ha2', he2]) (by linarith only [ha2, he]) (by linarith only [ha1', he1])
    have t3 := six_cp_sep_hi hbe k1 (by linarith only [hb2', he2]) (by linarith only [hb2, he]) (by linarith only [h2])
    linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, h1, h2, t1, t2, t3]

theorem six_cp_Ige (a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 : ℝ)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1/3)
    (hb1 : 1/2 ≤ b1) (hb1' : b1 ≤ 1) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 1/3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1/2) (hc2 : 1/3 ≤ c2) (hc2' : c2 ≤ 2/3)
    (he1 : 1/2 ≤ e1) (he1' : e1 ≤ 1) (he2 : 1/3 ≤ e2) (he2' : e2 ≤ 2/3)
    (hf1 : 0 ≤ f1) (hf1' : f1 ≤ 1/2) (hf2 : 2/3 ≤ f2) (hf2' : f2 ≤ 1)
    (hg1 : 1/2 ≤ g1) (hg1' : g1 ≤ 1) (hg2 : 2/3 ≤ g2) (hg2' : g2 ≤ 1)
    (hab : 13/36 < (a1 - b1)^2 + (a2 - b2)^2)
    (hac : 13/36 < (a1 - c1)^2 + (a2 - c2)^2)
    (hae : 13/36 < (a1 - e1)^2 + (a2 - e2)^2)
    (haf : 13/36 < (a1 - f1)^2 + (a2 - f2)^2)
    (hag : 13/36 < (a1 - g1)^2 + (a2 - g2)^2)
    (hbc : 13/36 < (b1 - c1)^2 + (b2 - c2)^2)
    (hbe : 13/36 < (b1 - e1)^2 + (b2 - e2)^2)
    (hbf : 13/36 < (b1 - f1)^2 + (b2 - f2)^2)
    (hbg : 13/36 < (b1 - g1)^2 + (b2 - g2)^2)
    (hce : 13/36 < (c1 - e1)^2 + (c2 - e2)^2)
    (hcf : 13/36 < (c1 - f1)^2 + (c2 - f2)^2)
    (hcg : 13/36 < (c1 - g1)^2 + (c2 - g2)^2)
    (hef : 13/36 < (e1 - f1)^2 + (e2 - f2)^2)
    (heg : 13/36 < (e1 - g1)^2 + (e2 - g2)^2)
    (hfg : 13/36 < (f1 - g1)^2 + (f2 - g2)^2)
    (hc : c2 ≤ 1/2) (he : 1/2 ≤ e2) (hac1 : a1 ≤ c1) (hge1 : g1 ≤ e1) : False := by
  have k1 : (1/3:ℝ)^2 + (1/2)^2 ≤ 13/36 := by norm_num
  have k2 : (1/2:ℝ)^2 + (1/3)^2 ≤ 13/36 := by norm_num
  have d1 := six_cp_sep_lo hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [hac1])
  have d2 := six_cp_sep_hi heg k1 (by linarith only [he2', hg2]) (by linarith only [hg2', he]) (by linarith only [hge1])
  have d3 := six_cp_sep_lo hfg k2 (by linarith only [hf2', hg2]) (by linarith only [hf2, hg2']) (by linarith only [hf1', hg1])
  have qac : 13/36 < c1^2 + c2^2 := by
    linarith only [hac, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg ha1 (show 0 ≤ 2*c1 - a1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3]), mul_nonneg ha2 (show 0 ≤ 2*c2 - a2 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  have qcf : 13/36 < c1^2 + (f2 - c2)^2 := by
    linarith only [hcf, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg hf1 (show 0 ≤ 2*c1 - f1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  have qcg : 13/36 < (g1 - c1)^2 + (g2 - c2)^2 := hcg.trans_eq (by ring)
  have qcb : 13/36 < (b1 - c1)^2 + c2^2 := by
    linarith only [hbc, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg hb2 (show 0 ≤ 2*c2 - b2 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  have qge : 13/36 < (1 - g1)^2 + (g2 - e2)^2 := by
    linarith only [heg, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg (show 0 ≤ 1 - e1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3]) (show 0 ≤ 1 + e1 - 2*g1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  have qfg : 13/36 < g1^2 + (f2 - g2)^2 := by
    linarith only [hfg, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg hf1 (show 0 ≤ 2*g1 - f1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  have qce : 13/36 < (1 - c1)^2 + (e2 - c2)^2 := by
    linarith only [hce, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3, mul_nonneg (show 0 ≤ 1 - e1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3]) (show 0 ≤ 1 + e1 - 2*c1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, d1, d2, d3])]
  rcases le_total b1 e1 with hbe1 | hbe1
  · have qbe : 13/36 < (1 - b1)^2 + e2^2 := by
      linarith only [hbe, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3, mul_nonneg (show 0 ≤ 1 - e1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3]) (show 0 ≤ 1 + e1 - 2*b1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3]),
        mul_nonneg hb2 (show 0 ≤ 2*e2 - b2 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3])]
    exact six_cp_redA c1 c2 g1 b1 e2 f2 g2 (by linarith only [hc1]) (by linarith only [hc1']) (by linarith only [hc2]) (by linarith only [hc]) (by linarith only [hg1]) (by linarith only [hg1']) (by linarith only [hb1]) (by linarith only [hb1']) (by linarith only [he]) (by linarith only [he2']) (by linarith only [hf2]) (by linarith only [hf2']) (by linarith only [hg2]) (by linarith only [hg2']) (by linarith only [hc1', hg1]) (by linarith only [hb1, hc1']) qac qcf qcg qcb qge qbe qfg qce
  · have qbe : 13/36 < (1 - e1)^2 + e2^2 := by
      linarith only [hbe, ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3, mul_nonneg (show 0 ≤ 1 - b1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3]) (show 0 ≤ 1 + b1 - 2*e1 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3]),
        mul_nonneg hb2 (show 0 ≤ 2*e2 - b2 by linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, hac1, hge1, hbe1, d1, d2, d3])]
    exact six_cp_redB c1 c2 g1 b1 e2 f2 g2 e1 (by linarith only [hc1]) (by linarith only [hc1']) (by linarith only [hc2]) (by linarith only [hc]) (by linarith only [hg1]) (by linarith only [hg1']) (by linarith only [hb1]) (by linarith only [hb1']) (by linarith only [he]) (by linarith only [he2']) (by linarith only [hf2]) (by linarith only [hf2']) (by linarith only [hg2]) (by linarith only [hg2']) (by linarith only [hc1', hg1]) (by linarith only [hb1, hc1']) (by linarith only [he1]) (by linarith only [he1']) (by linarith only [hbe1]) (by linarith only [d2]) qac qcf qcg qcb qge qbe qfg qce

theorem six_cp_IIge (a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 : ℝ)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1/3)
    (hb1 : 1/2 ≤ b1) (hb1' : b1 ≤ 1) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 1/3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1/2) (hc2 : 1/3 ≤ c2) (hc2' : c2 ≤ 2/3)
    (he1 : 1/2 ≤ e1) (he1' : e1 ≤ 1) (he2 : 1/3 ≤ e2) (he2' : e2 ≤ 2/3)
    (hf1 : 0 ≤ f1) (hf1' : f1 ≤ 1/2) (hf2 : 2/3 ≤ f2) (hf2' : f2 ≤ 1)
    (hg1 : 1/2 ≤ g1) (hg1' : g1 ≤ 1) (hg2 : 2/3 ≤ g2) (hg2' : g2 ≤ 1)
    (hab : 13/36 < (a1 - b1)^2 + (a2 - b2)^2)
    (hac : 13/36 < (a1 - c1)^2 + (a2 - c2)^2)
    (hae : 13/36 < (a1 - e1)^2 + (a2 - e2)^2)
    (haf : 13/36 < (a1 - f1)^2 + (a2 - f2)^2)
    (hag : 13/36 < (a1 - g1)^2 + (a2 - g2)^2)
    (hbc : 13/36 < (b1 - c1)^2 + (b2 - c2)^2)
    (hbe : 13/36 < (b1 - e1)^2 + (b2 - e2)^2)
    (hbf : 13/36 < (b1 - f1)^2 + (b2 - f2)^2)
    (hbg : 13/36 < (b1 - g1)^2 + (b2 - g2)^2)
    (hce : 13/36 < (c1 - e1)^2 + (c2 - e2)^2)
    (hcf : 13/36 < (c1 - f1)^2 + (c2 - f2)^2)
    (hcg : 13/36 < (c1 - g1)^2 + (c2 - g2)^2)
    (hef : 13/36 < (e1 - f1)^2 + (e2 - f2)^2)
    (heg : 13/36 < (e1 - g1)^2 + (e2 - g2)^2)
    (hfg : 13/36 < (f1 - g1)^2 + (f2 - g2)^2)
    (hc : c2 ≤ 1/2) (he : 1/2 ≤ e2) (hac1 : c1 ≤ a1) (hge1 : g1 ≤ e1) : False := by
  have k1 : (1/3:ℝ)^2 + (1/2)^2 ≤ 13/36 := by norm_num
  have k2 : (1/2:ℝ)^2 + (1/3)^2 ≤ 13/36 := by norm_num
  have r1 := six_cp_sep_hi hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [hac1])
  have r2 := six_cp_sep_lo hab k2 (by linarith only [ha2', hb2]) (by linarith only [ha2, hb2']) (by linarith only [ha1', hb1])
  have r3 := six_cp_sep_hi heg k1 (by linarith only [he2', hg2]) (by linarith only [hg2', he]) (by linarith only [hge1])
  have r4 := six_cp_sep_lo hfg k2 (by linarith only [hf2', hg2]) (by linarith only [hf2, hg2']) (by linarith only [hf1', hg1])
  have r5 := six_cp_sepy_lo hac k1 (by linarith only [ha1', hc1]) (by linarith only [hac1]) (by linarith only [ha2', hc2])
  have r6 := six_cp_sepy_lo hcf k1 (by linarith only [hc1', hf1]) (by linarith only [hc1, hf1']) (by linarith only [hc2', hf2])
  have r7 := six_cp_sepy_lo hbe k1 (by linarith only [hb1', he1]) (by linarith only [hb1, he1']) (by linarith only [hb2', he2])
  have r8 := six_cp_sepy_lo heg k1 (by linarith only [he1', hg1]) (by linarith only [hge1]) (by linarith only [he2', hg2])
  have r9 := six_cp_sep_lo hce k2 (by linarith only [hc2', he2]) (by linarith only [hc2, he2']) (by linarith only [hc1', he1])
  exact absurd (show (0:ℝ) < 0 by
      linear_combination (45/221) * hab +
        (63/221) * hac +
        (15/221) * hbe +
        (49/221) * hcf +
        (21/221) * heg +
        (21/221) * hfg +
        (20/221) * ha2 +
        (25/221) * hb1' +
        (3/221) * hc1 +
        (2/221) * hf1 +
        (42/221) * hf2' +
        (14/221) * hg2' +
        (7/221) * r3 +
        (30/221) * mul_nonneg (sub_nonneg.2 hb1') (sub_nonneg.2 hc1') +
        (30/221) * mul_nonneg (sub_nonneg.2 hb1') (sub_nonneg.2 hf1') +
        (6/17) * mul_nonneg (sub_nonneg.2 hb1') (sub_nonneg.2 (le_of_lt r1)) +
        (60/221) * mul_nonneg (sub_nonneg.2 hb1') (sub_nonneg.2 (le_of_lt r2)) +
        (94/221) * mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hc1') +
        (30/221) * mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 he1) +
        (4/13) * mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hf1) +
        (18/221) * mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 (le_of_lt r1)) +
        (36/221) * mul_nonneg (sub_nonneg.2 he1) (sub_nonneg.2 he1') +
        (30/221) * mul_nonneg (sub_nonneg.2 he1') (sub_nonneg.2 hf1') +
        (58/221) * mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 hf1') +
        (12/221) * mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 (le_of_lt r3)) +
        (12/221) * mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 (le_of_lt r4)) +
        (108/221) * mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 ha2') +
        (90/221) * mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hb2) +
        (42/221) * mul_nonneg (sub_nonneg.2 ha2) (sub_nonneg.2 hc2) +
        (30/221) * mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hb2') +
        (30/221) * mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 (le_of_lt r7)) +
        (28/221) * mul_nonneg (sub_nonneg.2 hc2) (sub_nonneg.2 (le_of_lt r6)) +
        (84/221) * mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 (le_of_lt r5)) +
        (36/221) * mul_nonneg (sub_nonneg.2 he) (sub_nonneg.2 hg2') +
        (36/221) * mul_nonneg (sub_nonneg.2 he) (sub_nonneg.2 (le_of_lt r8)) +
        (42/221) * mul_nonneg (sub_nonneg.2 hf2') (sub_nonneg.2 hg2') +
        (70/221) * mul_nonneg (sub_nonneg.2 hf2') (sub_nonneg.2 (le_of_lt r6)) +
        (42/221) * mul_nonneg (sub_nonneg.2 hg2') (sub_nonneg.2 (le_of_lt r8)) +
        (108/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r1)) (sub_nonneg.2 (le_of_lt r2)) +
        (30/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r1)) (sub_nonneg.2 (le_of_lt r3)) +
        (30/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r1)) (sub_nonneg.2 (le_of_lt r4)) +
        (30/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r2)) (sub_nonneg.2 (le_of_lt r3)) +
        (30/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r2)) (sub_nonneg.2 (le_of_lt r4)) +
        (42/221) * mul_nonneg (sub_nonneg.2 (le_of_lt r3)) (sub_nonneg.2 (le_of_lt r4))) (lt_irrefl 0)

theorem six_cp_K (a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 : ℝ)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1/3)
    (hb1 : 1/2 ≤ b1) (hb1' : b1 ≤ 1) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 1/3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1/2) (hc2 : 1/3 ≤ c2) (hc2' : c2 ≤ 2/3)
    (he1 : 1/2 ≤ e1) (he1' : e1 ≤ 1) (he2 : 1/3 ≤ e2) (he2' : e2 ≤ 2/3)
    (hf1 : 0 ≤ f1) (hf1' : f1 ≤ 1/2) (hf2 : 2/3 ≤ f2) (hf2' : f2 ≤ 1)
    (hg1 : 1/2 ≤ g1) (hg1' : g1 ≤ 1) (hg2 : 2/3 ≤ g2) (hg2' : g2 ≤ 1)
    (hab : 13/36 < (a1 - b1)^2 + (a2 - b2)^2)
    (hac : 13/36 < (a1 - c1)^2 + (a2 - c2)^2)
    (hae : 13/36 < (a1 - e1)^2 + (a2 - e2)^2)
    (haf : 13/36 < (a1 - f1)^2 + (a2 - f2)^2)
    (hag : 13/36 < (a1 - g1)^2 + (a2 - g2)^2)
    (hbc : 13/36 < (b1 - c1)^2 + (b2 - c2)^2)
    (hbe : 13/36 < (b1 - e1)^2 + (b2 - e2)^2)
    (hbf : 13/36 < (b1 - f1)^2 + (b2 - f2)^2)
    (hbg : 13/36 < (b1 - g1)^2 + (b2 - g2)^2)
    (hce : 13/36 < (c1 - e1)^2 + (c2 - e2)^2)
    (hcf : 13/36 < (c1 - f1)^2 + (c2 - f2)^2)
    (hcg : 13/36 < (c1 - g1)^2 + (c2 - g2)^2)
    (hef : 13/36 < (e1 - f1)^2 + (e2 - f2)^2)
    (heg : 13/36 < (e1 - g1)^2 + (e2 - g2)^2)
    (hfg : 13/36 < (f1 - g1)^2 + (f2 - g2)^2)
    (hc : c2 ≤ 1/2) (he : 1/2 ≤ e2) : False := by
  have k1 : (1/3:ℝ)^2 + (1/2)^2 ≤ 13/36 := by norm_num
  rcases le_total a1 c1 with h1 | h1 <;> rcases le_total g1 e1 with h2 | h2
  · exact six_cp_Ige a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 ha1 ha1' ha2 ha2' hb1 hb1' hb2 hb2' hc1 hc1' hc2 hc2' he1 he1' he2 he2' hf1 hf1' hf2 hf2' hg1 hg1' hg2 hg2' hab hac hae haf hag hbc hbe hbf hbg hce hcf hcg hef heg hfg hc he h1 h2
  · have d1 := six_cp_sep_lo hac k1 (by linarith only [ha2', hc2]) (by linarith only [ha2, hc]) (by linarith only [h1])
    have d2 := six_cp_sep_lo heg k1 (by linarith only [he2', hg2]) (by linarith only [hg2', he]) (by linarith only [h2])
    have d3 := six_cp_sep_lo hce k1 (by linarith only [hc2', he2]) (by linarith only [hc2, he2']) (by linarith only [hc1', he1])
    linarith only [ha1, ha1', ha2, ha2', hb1, hb1', hb2, hb2', hc1, hc1', hc2, hc2', he1, he1', he2, he2', hf1, hf1', hf2, hf2', hg1, hg1', hg2, hg2', hc, he, h1, h2, d1, d2, d3]
  · exact six_cp_IIge a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 ha1 ha1' ha2 ha2' hb1 hb1' hb2 hb2' hc1 hc1' hc2 hc2' he1 he1' he2 he2' hf1 hf1' hf2 hf2' hg1 hg1' hg2 hg2' hab hac hae haf hag hbc hbe hbf hbg hce hcf hcg hef heg hfg hc he h1 h2
  · exact six_cp_Ige (1 - g1) (1 - g2) (1 - f1) (1 - f2) (1 - e1) (1 - e2) (1 - c1) (1 - c2) (1 - b1) (1 - b2) (1 - a1) (1 - a2) (by linarith only [hg1']) (by linarith only [hg1]) (by linarith only [hg2']) (by linarith only [hg2]) (by linarith only [hf1']) (by linarith only [hf1]) (by linarith only [hf2']) (by linarith only [hf2]) (by linarith only [he1']) (by linarith only [he1]) (by linarith only [he2']) (by linarith only [he2]) (by linarith only [hc1']) (by linarith only [hc1]) (by linarith only [hc2']) (by linarith only [hc2]) (by linarith only [hb1']) (by linarith only [hb1]) (by linarith only [hb2']) (by linarith only [hb2]) (by linarith only [ha1']) (by linarith only [ha1]) (by linarith only [ha2']) (by linarith only [ha2]) (hfg.trans_eq (by ring)) (heg.trans_eq (by ring)) (hcg.trans_eq (by ring)) (hbg.trans_eq (by ring)) (hag.trans_eq (by ring)) (hef.trans_eq (by ring)) (hcf.trans_eq (by ring)) (hbf.trans_eq (by ring)) (haf.trans_eq (by ring)) (hce.trans_eq (by ring)) (hbe.trans_eq (by ring)) (hae.trans_eq (by ring)) (hbc.trans_eq (by ring)) (hac.trans_eq (by ring)) (hab.trans_eq (by ring)) (by linarith only [he]) (by linarith only [hc]) (by linarith only [h2]) (by linarith only [h1])

theorem six_cp_core (a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 : ℝ)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (ha2 : 0 ≤ a2) (ha2' : a2 ≤ 1/3)
    (hb1 : 1/2 ≤ b1) (hb1' : b1 ≤ 1) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 1/3)
    (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1/2) (hc2 : 1/3 ≤ c2) (hc2' : c2 ≤ 2/3)
    (he1 : 1/2 ≤ e1) (he1' : e1 ≤ 1) (he2 : 1/3 ≤ e2) (he2' : e2 ≤ 2/3)
    (hf1 : 0 ≤ f1) (hf1' : f1 ≤ 1/2) (hf2 : 2/3 ≤ f2) (hf2' : f2 ≤ 1)
    (hg1 : 1/2 ≤ g1) (hg1' : g1 ≤ 1) (hg2 : 2/3 ≤ g2) (hg2' : g2 ≤ 1)
    (hab : 13/36 < (a1 - b1)^2 + (a2 - b2)^2)
    (hac : 13/36 < (a1 - c1)^2 + (a2 - c2)^2)
    (hae : 13/36 < (a1 - e1)^2 + (a2 - e2)^2)
    (haf : 13/36 < (a1 - f1)^2 + (a2 - f2)^2)
    (hag : 13/36 < (a1 - g1)^2 + (a2 - g2)^2)
    (hbc : 13/36 < (b1 - c1)^2 + (b2 - c2)^2)
    (hbe : 13/36 < (b1 - e1)^2 + (b2 - e2)^2)
    (hbf : 13/36 < (b1 - f1)^2 + (b2 - f2)^2)
    (hbg : 13/36 < (b1 - g1)^2 + (b2 - g2)^2)
    (hce : 13/36 < (c1 - e1)^2 + (c2 - e2)^2)
    (hcf : 13/36 < (c1 - f1)^2 + (c2 - f2)^2)
    (hcg : 13/36 < (c1 - g1)^2 + (c2 - g2)^2)
    (hef : 13/36 < (e1 - f1)^2 + (e2 - f2)^2)
    (heg : 13/36 < (e1 - g1)^2 + (e2 - g2)^2)
    (hfg : 13/36 < (f1 - g1)^2 + (f2 - g2)^2)
     : False := by
  rcases le_total c2 (1/2) with hc | hc <;> rcases le_total e2 (1/2) with he | he
  · exact six_cp_low a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 ha1 ha1' ha2 ha2' hb1 hb1' hb2 hb2' hc1 hc1' hc2 hc2' he1 he1' he2 he2' hf1 hf1' hf2 hf2' hg1 hg1' hg2 hg2' hab hac hae haf hag hbc hbe hbf hbg hce hcf hcg hef heg hfg hc he
  · exact six_cp_K a1 a2 b1 b2 c1 c2 e1 e2 f1 f2 g1 g2 ha1 ha1' ha2 ha2' hb1 hb1' hb2 hb2' hc1 hc1' hc2 hc2' he1 he1' he2 he2' hf1 hf1' hf2 hf2' hg1 hg1' hg2 hg2' hab hac hae haf hag hbc hbe hbf hbg hce hcf hcg hef heg hfg hc he
  · exact six_cp_K (1 - b1) b2 (1 - a1) a2 (1 - e1) e2 (1 - c1) c2 (1 - g1) g2 (1 - f1) f2 (by linarith only [hb1']) (by linarith only [hb1]) (by linarith only [hb2]) (by linarith only [hb2']) (by linarith only [ha1']) (by linarith only [ha1]) (by linarith only [ha2]) (by linarith only [ha2']) (by linarith only [he1']) (by linarith only [he1]) (by linarith only [he2]) (by linarith only [he2']) (by linarith only [hc1']) (by linarith only [hc1]) (by linarith only [hc2]) (by linarith only [hc2']) (by linarith only [hg1']) (by linarith only [hg1]) (by linarith only [hg2]) (by linarith only [hg2']) (by linarith only [hf1']) (by linarith only [hf1]) (by linarith only [hf2]) (by linarith only [hf2']) (hab.trans_eq (by ring)) (hbe.trans_eq (by ring)) (hbc.trans_eq (by ring)) (hbg.trans_eq (by ring)) (hbf.trans_eq (by ring)) (hae.trans_eq (by ring)) (hac.trans_eq (by ring)) (hag.trans_eq (by ring)) (haf.trans_eq (by ring)) (hce.trans_eq (by ring)) (heg.trans_eq (by ring)) (hef.trans_eq (by ring)) (hcg.trans_eq (by ring)) (hcf.trans_eq (by ring)) (hfg.trans_eq (by ring)) (by linarith only [he]) (by linarith only [hc])
  · exact six_cp_low f1 (1 - f2) g1 (1 - g2) c1 (1 - c2) e1 (1 - e2) a1 (1 - a2) b1 (1 - b2) (by linarith only [hf1]) (by linarith only [hf1']) (by linarith only [hf2']) (by linarith only [hf2]) (by linarith only [hg1]) (by linarith only [hg1']) (by linarith only [hg2']) (by linarith only [hg2]) (by linarith only [hc1]) (by linarith only [hc1']) (by linarith only [hc2']) (by linarith only [hc2]) (by linarith only [he1]) (by linarith only [he1']) (by linarith only [he2']) (by linarith only [he2]) (by linarith only [ha1]) (by linarith only [ha1']) (by linarith only [ha2']) (by linarith only [ha2]) (by linarith only [hb1]) (by linarith only [hb1']) (by linarith only [hb2']) (by linarith only [hb2]) (hfg.trans_eq (by ring)) (hcf.trans_eq (by ring)) (hef.trans_eq (by ring)) (haf.trans_eq (by ring)) (hbf.trans_eq (by ring)) (hcg.trans_eq (by ring)) (heg.trans_eq (by ring)) (hag.trans_eq (by ring)) (hbg.trans_eq (by ring)) (hce.trans_eq (by ring)) (hac.trans_eq (by ring)) (hbc.trans_eq (by ring)) (hae.trans_eq (by ring)) (hbe.trans_eq (by ring)) (hab.trans_eq (by ring)) (by linarith only [hc]) (by linarith only [he])

/-- Column index of a point: `0` if `x < 1/2`, else `1`. -/
noncomputable def six_cp_col (q : Point) : Fin 2 := if q.1 < 1/2 then 0 else 1

/-- Row index of a point: `0` if `y < 1/3`, `1` if `y < 2/3`, else `2`. -/
noncomputable def six_cp_row (q : Point) : Fin 3 :=
  if q.2 < 1/3 then 0 else if q.2 < 2/3 then 1 else 2

theorem six_cp_col_eq {q r : Point} (hq : 0 ≤ q.1 ∧ q.1 ≤ 1) (hr : 0 ≤ r.1 ∧ r.1 ≤ 1)
    (h : six_cp_col q = six_cp_col r) : q.1 - r.1 ≤ 1/2 ∧ r.1 - q.1 ≤ 1/2 := by
  unfold six_cp_col at h
  split_ifs at h with h1 h2 h2 <;> first | exact absurd h (by decide) | constructor <;> linarith

theorem six_cp_row_eq {q r : Point} (hq : 0 ≤ q.2 ∧ q.2 ≤ 1) (hr : 0 ≤ r.2 ∧ r.2 ≤ 1)
    (h : six_cp_row q = six_cp_row r) : q.2 - r.2 ≤ 1/3 ∧ r.2 - q.2 ≤ 1/3 := by
  unfold six_cp_row at h
  split_ifs at h <;> first | exact absurd h (by decide) | constructor <;> linarith

theorem six_cp_close {x1 y1 x2 y2 : ℝ} (hx1 : x1 - x2 ≤ 1/2) (hx2 : x2 - x1 ≤ 1/2)
    (hy1 : y1 - y2 ≤ 1/3) (hy2 : y2 - y1 ≤ 1/3) : (x1 - x2)^2 + (y1 - y2)^2 ≤ 13/36 := by
  nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hx2),
    mul_nonneg (sub_nonneg.2 hy1) (sub_nonneg.2 hy2)]

theorem six_cp_col0 {q : Point} (h : six_cp_col q = 0) : q.1 ≤ 1/2 := by
  unfold six_cp_col at h; split_ifs at h with h1
  · linarith
  · exact absurd h (by decide)

theorem six_cp_col1 {q : Point} (h : six_cp_col q = 1) : 1/2 ≤ q.1 := by
  unfold six_cp_col at h; split_ifs at h with h1
  · exact absurd h (by decide)
  · linarith

theorem six_cp_row0 {q : Point} (h : six_cp_row q = 0) : q.2 ≤ 1/3 := by
  unfold six_cp_row at h; split_ifs at h with h1 h2
  · linarith
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem six_cp_row1 {q : Point} (h : six_cp_row q = 1) : 1/3 ≤ q.2 ∧ q.2 ≤ 2/3 := by
  unfold six_cp_row at h; split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · constructor <;> linarith
  · exact absurd h (by decide)

theorem six_cp_row2 {q : Point} (h : six_cp_row q = 2) : 2/3 ≤ q.2 := by
  unfold six_cp_row at h; split_ifs at h with h1 h2
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · linarith

theorem six_unit_square_close_pair : ∀ p : Fin 6 → Point, (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) → ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (13 : ℝ) / 36 := by
  intro p hp
  by_contra hcon
  push_neg at hcon
  let cl : Fin 6 → Fin 2 × Fin 3 := fun i => (six_cp_col (p i), six_cp_row (p i))
  have hinj : Function.Injective cl := by
    intro i j hij
    by_contra hne
    have h1 := hcon i j hne
    have hc := six_cp_col_eq ⟨(hp i).1, (hp i).2.1⟩ ⟨(hp j).1, (hp j).2.1⟩ (congrArg Prod.fst hij)
    have hr := six_cp_row_eq ⟨(hp i).2.2.1, (hp i).2.2.2⟩ ⟨(hp j).2.2.1, (hp j).2.2.2⟩
      (congrArg Prod.snd hij)
    exact absurd (six_cp_close hc.1 hc.2 hr.1 hr.2) (not_le.2 h1)
  have hbij : Function.Bijective cl :=
    (Fintype.bijective_iff_injective_and_card cl).2 ⟨hinj, by simp⟩
  obtain ⟨ia, hA⟩ := hbij.2 (0, 0)
  obtain ⟨ib, hB⟩ := hbij.2 (1, 0)
  obtain ⟨ic, hC⟩ := hbij.2 (0, 1)
  obtain ⟨ie, hE⟩ := hbij.2 (1, 1)
  obtain ⟨jf, hF⟩ := hbij.2 (0, 2)
  obtain ⟨jg, hG⟩ := hbij.2 (1, 2)
  have hne : ∀ i j : Fin 6, cl i ≠ cl j → 13/36 < sqDist (p i) (p j) :=
    fun i j h => hcon i j (ne_of_apply_ne cl h)
  simp only [cl, Prod.mk.injEq] at hA hB hC hE hF hG
  exact six_cp_core (p ia).1 (p ia).2 (p ib).1 (p ib).2 (p ic).1 (p ic).2 (p ie).1 (p ie).2
    (p jf).1 (p jf).2 (p jg).1 (p jg).2
    (hp ia).1 (six_cp_col0 hA.1) (hp ia).2.2.1 (six_cp_row0 hA.2)
    (six_cp_col1 hB.1) (hp ib).2.1 (hp ib).2.2.1 (six_cp_row0 hB.2)
    (hp ic).1 (six_cp_col0 hC.1) (six_cp_row1 hC.2).1 (six_cp_row1 hC.2).2
    (six_cp_col1 hE.1) (hp ie).2.1 (six_cp_row1 hE.2).1 (six_cp_row1 hE.2).2
    (hp jf).1 (six_cp_col0 hF.1) (six_cp_row2 hF.2) (hp jf).2.2.2
    (six_cp_col1 hG.1) (hp jg).2.1 (six_cp_row2 hG.2) (hp jg).2.2.2
    (hne ia ib (by simp [cl, hA, hB])) (hne ia ic (by simp [cl, hA, hC]))
    (hne ia ie (by simp [cl, hA, hE])) (hne ia jf (by simp [cl, hA, hF]))
    (hne ia jg (by simp [cl, hA, hG])) (hne ib ic (by simp [cl, hB, hC]))
    (hne ib ie (by simp [cl, hB, hE])) (hne ib jf (by simp [cl, hB, hF]))
    (hne ib jg (by simp [cl, hB, hG])) (hne ic ie (by simp [cl, hC, hE]))
    (hne ic jf (by simp [cl, hC, hF])) (hne ic jg (by simp [cl, hC, hG]))
    (hne ie jf (by simp [cl, hE, hF])) (hne ie jg (by simp [cl, hE, hG]))
    (hne jf jg (by simp [cl, hF, hG]))

end CirclePackingConstants


-- Platform entry point: restates the target verbatim.
namespace CirclePackingConstants

theorem _root_.solution : ∀ p : Fin 6 → Point, (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) → ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (13 : ℝ) / 36 := by
  apply @CirclePackingConstants.six_unit_square_close_pair <;> assumption

end CirclePackingConstants
